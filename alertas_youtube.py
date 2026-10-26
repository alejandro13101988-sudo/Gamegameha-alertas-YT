"""
Alertas de anuncios y tráilers de GameGameHa.

Vigila los canales de YouTube de compañías y estudios (lista en canales.txt)
y avisa por Telegram en cuanto suben un anuncio, un reveal, un tráiler o
anuncian un evento (State of Play, Nintendo Direct, showcases...), sin esperar
a que lo publique ninguna revista.

Cómo funciona (todo gratis, sin API de YouTube):
  * Cada canal tiene un feed RSS público de vídeos recientes.
  * El script lo consulta, se queda con los vídeos subidos en las últimas
    VENTANA_HORAS horas cuyo título parece un anuncio/tráiler, y los manda.
  * estado_alertas.json recuerda qué se ha avisado ya (no se repite nada) y
    los IDs de canal ya resueltos.

Variables de entorno:
  TELEGRAM_BOT_TOKEN   token del bot (obligatoria)
  TELEGRAM_CHAT_ID     chat/grupo destino (obligatoria)
  ALERTAS_CHAT_ID      (opcional) otro chat solo para alertas; si existe,
                       tiene prioridad sobre TELEGRAM_CHAT_ID
  ALERTAS_THREAD_ID    (opcional) id del tema (topic) si el grupo usa temas

Uso local de prueba, sin enviar nada a Telegram:
  python alertas_youtube.py --dry-run
"""

import os
import re
import sys
import json
import html
import time
import difflib
import argparse
import unicodedata
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone

import feedparser
import requests

# --------------------------------------------------------------------------
# CONFIGURACIÓN
# --------------------------------------------------------------------------

VENTANA_HORAS = 6                 # solo se avisa de vídeos subidos hace menos de esto
MAX_ALERTAS_POR_EJECUCION = 15    # tope para no saturar Telegram
UMBRAL_TITULO_PARECIDO = 0.85     # evita avisar dos veces del mismo tráiler subido por 2 canales
HORAS_MEMORIA_TITULOS = 48
HILOS = 8
TIMEOUT_RED = 15
ARCHIVO_ESTADO = "estado_alertas.json"
ARCHIVO_CANALES = "canales.txt"

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)

# Palabras que hacen que un vídeo valga la pena (modo normal).
PATRON_ANUNCIO = re.compile(
    r"announce|announcement|reveal|world premiere|teaser|trailer|first look|"
    r"release date|launch date|gameplay|cinematic|showcase|state of play|"
    r"\bdirect\b|presents|coming (soon|20\d\d)|\b20(2[6-9]|3[0-2])\b|"
    r"anunci|revela|tr[aá]iler|presentaci[oó]n|avance",
    re.IGNORECASE,
)

# Modo "estricto" (medios y eventos que suben muchísimo): solo anuncios de verdad.
PATRON_ESTRICTO = re.compile(
    r"announce|announcement|reveal|world premiere|first look|teaser|"
    r"release date|launch date|state of play|\bdirect\b|showcase|presents|"
    r"anunci|revela|presentaci[oó]n",
    re.IGNORECASE,
)

# Vídeos que casi nunca son un anuncio.
PATRON_EXCLUIR = re.compile(
    r"giveaway|sweepstakes|sorteo|reaction|reacts? to|unboxing|review|recap|"
    r"compilation|best of|top \d+|merch|soundtrack|\bost\b|how to|tutorial|"
    r"walkthrough|let'?s play|highlights|podcast",
    re.IGNORECASE,
)

PATRON_EVENTO = re.compile(
    r"state of play|\bdirect\b|showcase|presents|conference|summer game fest|"
    r"gamescom|game awards|tokyo game show|xbox games|opening night live",
    re.IGNORECASE,
)
PATRON_ANUNCIO_FUERTE = re.compile(
    r"announce|announcement|reveal|world premiere|first look|anunci|revela",
    re.IGNORECASE,
)

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.environ.get("ALERTAS_CHAT_ID") or os.environ.get("TELEGRAM_CHAT_ID")
TELEGRAM_THREAD_ID = os.environ.get("ALERTAS_THREAD_ID") or None


# --------------------------------------------------------------------------
# ESTADO
# --------------------------------------------------------------------------


def estado_vacio():
    return {"alertados": [], "titulos": [], "canales": {}, "fallos_avisados": []}


def cargar_estado():
    if os.path.exists(ARCHIVO_ESTADO):
        try:
            with open(ARCHIVO_ESTADO, "r", encoding="utf-8") as f:
                datos = json.load(f)
            base = estado_vacio()
            base.update(datos)
            return base
        except Exception as e:
            print(f"[aviso] estado ilegible, se empieza de cero: {e}", file=sys.stderr)
    return estado_vacio()


def guardar_estado(estado):
    estado["alertados"] = estado["alertados"][-800:]
    estado["titulos"] = estado["titulos"][-150:]
    with open(ARCHIVO_ESTADO, "w", encoding="utf-8") as f:
        json.dump(estado, f, ensure_ascii=False, indent=2, sort_keys=True)


# --------------------------------------------------------------------------
# LISTA DE CANALES
# --------------------------------------------------------------------------


def leer_canales(ruta=ARCHIVO_CANALES):
    """Devuelve una lista de dicts {ident, estricto}. ident es @handle o UC..."""
    canales = []
    vistos = set()
    with open(ruta, "r", encoding="utf-8") as f:
        for linea in f:
            linea = linea.split("#", 1)[0].strip()
            if not linea:
                continue
            partes = [p.strip() for p in linea.split("|")]
            ident = partes[0]
            if not ident or ident.lower() in vistos:
                continue
            vistos.add(ident.lower())
            estricto = any(p.lower() == "estricto" for p in partes[1:])
            canales.append({"ident": ident, "estricto": estricto})
    return canales


PATRON_ID_CANAL = re.compile(r"^UC[\w-]{22}$")


def resolver_channel_id(ident):
    """De '@Handle' (o 'UC...') saca el channel_id. None si no se pudo."""
    if PATRON_ID_CANAL.match(ident):
        return ident
    handle = ident if ident.startswith("@") else f"@{ident}"
    try:
        resp = requests.get(
            f"https://www.youtube.com/{handle}",
            headers={"User-Agent": USER_AGENT, "Accept-Language": "en-US,en;q=0.9"},
            cookies={"CONSENT": "YES+1", "SOCS": "CAI"},
            timeout=TIMEOUT_RED,
        )
        if resp.status_code != 200:
            return None
        texto = resp.text
        for patron in (
            r'<link rel="canonical" href="https://www\.youtube\.com/channel/(UC[\w-]{22})"',
            r"feeds/videos\.xml\?channel_id=(UC[\w-]{22})",
            r'"externalId":"(UC[\w-]{22})"',
            r'"channelId":"(UC[\w-]{22})"',
        ):
            m = re.search(patron, texto)
            if m:
                return m.group(1)
    except Exception as e:
        print(f"  [aviso] no se pudo resolver {handle}: {e}", file=sys.stderr)
    return None


# --------------------------------------------------------------------------
# LECTURA DE FEEDS Y FILTROS
# --------------------------------------------------------------------------


def fecha_entrada(entrada):
    for campo in ("published_parsed", "updated_parsed"):
        valor = entrada.get(campo)
        if valor:
            return datetime(*valor[:6], tzinfo=timezone.utc)
    return None


def videos_de_feed(contenido):
    """Convierte el XML del feed en una lista de vídeos."""
    feed = feedparser.parse(contenido)
    videos = []
    nombre_canal = (feed.feed.get("title") or "").strip()
    for e in feed.entries:
        enlace = (e.get("link") or "").strip()
        video_id = e.get("yt_videoid") or ""
        if not video_id:
            m = re.search(r"[?&]v=([\w-]{11})", enlace)
            video_id = m.group(1) if m else ""
        if not video_id or "/shorts/" in enlace:
            continue
        publicado = fecha_entrada(e)
        if not publicado:
            continue
        videos.append(
            {
                "id": video_id,
                "titulo": (e.get("title") or "").strip(),
                "canal": nombre_canal or (e.get("author") or "").strip(),
                "publicado": publicado,
                "url": f"https://www.youtube.com/watch?v={video_id}",
            }
        )
    return videos


def descargar_feed(channel_id):
    try:
        resp = requests.get(
            f"https://www.youtube.com/feeds/videos.xml?channel_id={channel_id}",
            headers={"User-Agent": USER_AGENT},
            timeout=TIMEOUT_RED,
        )
        if resp.status_code != 200:
            print(f"  [aviso] feed {channel_id} respondió {resp.status_code}", file=sys.stderr)
            return None
        return resp.content
    except Exception as e:
        print(f"  [aviso] no se pudo leer el feed {channel_id}: {e}", file=sys.stderr)
        return None


def pasa_filtro(titulo, estricto):
    if PATRON_EXCLUIR.search(titulo):
        return False
    patron = PATRON_ESTRICTO if estricto else PATRON_ANUNCIO
    return bool(patron.search(titulo))


def clasificar(titulo):
    if PATRON_EVENTO.search(titulo):
        return "📅 Evento"
    if PATRON_ANUNCIO_FUERTE.search(titulo):
        return "🚨 Anuncio"
    return "🎬 Tráiler"


def normalizar(t):
    t = unicodedata.normalize("NFKD", t.lower()).encode("ascii", "ignore").decode("ascii")
    return re.sub(r"\s+", " ", re.sub(r"[^a-z0-9\s]", " ", t)).strip()


def es_repetido_de_otro_canal(video, titulos_recientes):
    """True si otro canal ya avisó de un título casi idéntico hace poco."""
    n = normalizar(video["titulo"])
    for previo in titulos_recientes:
        if previo.get("canal") == video["canal"]:
            continue
        if difflib.SequenceMatcher(None, n, previo.get("n", "")).ratio() >= UMBRAL_TITULO_PARECIDO:
            return True
    return False


# --------------------------------------------------------------------------
# TELEGRAM
# --------------------------------------------------------------------------


def base_telegram(metodo):
    return f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/{metodo}"


def datos_comunes():
    datos = {"chat_id": TELEGRAM_CHAT_ID, "parse_mode": "HTML"}
    if TELEGRAM_THREAD_ID:
        datos["message_thread_id"] = TELEGRAM_THREAD_ID
    return datos


def enviar_texto(texto, preview=False):
    datos = datos_comunes()
    datos.update({"text": texto[:4000], "disable_web_page_preview": not preview})
    resp = requests.post(base_telegram("sendMessage"), data=datos, timeout=30)
    if resp.status_code != 200:
        print(f"[error] Telegram (mensaje) {resp.status_code}: {resp.text}", file=sys.stderr)
        return False
    return True


def enviar_foto(url_foto, pie):
    datos = datos_comunes()
    datos.update({"photo": url_foto, "caption": pie[:1024]})
    resp = requests.post(base_telegram("sendPhoto"), data=datos, timeout=30)
    return resp.status_code == 200


def texto_alerta(video):
    etiqueta = clasificar(video["titulo"])
    canal = html.escape(video["canal"] or "YouTube")
    titulo = html.escape(video["titulo"])
    return (
        f"{etiqueta} · <b>{canal}</b>\n"
        f"{titulo}\n"
        f'▶️ <a href="{video["url"]}">Ver en YouTube</a>'
    )


def enviar_alerta(video):
    texto = texto_alerta(video)
    for calidad in ("maxresdefault", "hqdefault"):
        miniatura = f"https://i.ytimg.com/vi/{video['id']}/{calidad}.jpg"
        if enviar_foto(miniatura, texto):
            return True
    return enviar_texto(texto, preview=True)


# --------------------------------------------------------------------------
# MAIN
# --------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true", help="no envía nada a Telegram, solo muestra")
    args = parser.parse_args()

    if not args.dry_run and (not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID):
        print("Faltan TELEGRAM_BOT_TOKEN y/o TELEGRAM_CHAT_ID.", file=sys.stderr)
        sys.exit(1)

    estado = cargar_estado()
    cambios = False
    canales = leer_canales()
    ahora = datetime.now(timezone.utc)
    limite = ahora - timedelta(hours=VENTANA_HORAS)

    # 1) resolver los @handle que aún no tenemos (solo la primera vez de cada uno)
    pendientes = [c for c in canales if c["ident"] not in estado["canales"] and not PATRON_ID_CANAL.match(c["ident"])]
    if pendientes:
        print(f"Resolviendo {len(pendientes)} canal(es) nuevo(s)...")
        with ThreadPoolExecutor(max_workers=HILOS) as pool:
            ids = list(pool.map(lambda c: resolver_channel_id(c["ident"]), pendientes))
        for c, cid in zip(pendientes, ids):
            if cid:
                estado["canales"][c["ident"]] = cid
                cambios = True
                if c["ident"] in estado["fallos_avisados"]:
                    estado["fallos_avisados"].remove(c["ident"])
            else:
                print(f"  [aviso] no se pudo resolver {c['ident']}")

    for c in canales:
        c["id"] = c["ident"] if PATRON_ID_CANAL.match(c["ident"]) else estado["canales"].get(c["ident"])

    # 2) avisar UNA vez de los canales que no existen / no se pueden resolver
    fallos_nuevos = [c["ident"] for c in canales if not c["id"] and c["ident"] not in estado["fallos_avisados"]]
    if fallos_nuevos:
        lista = "\n".join(f"• {html.escape(f)}" for f in fallos_nuevos)
        msg = (
            "⚠️ <b>Alertas de YouTube</b>: no he podido localizar estos canales "
            "(revisa que el @nombre esté bien escrito en canales.txt):\n" + lista
        )
        if args.dry_run:
            print(msg)
            enviado = True
        else:
            enviado = enviar_texto(msg)
        if enviado:
            estado["fallos_avisados"].extend(fallos_nuevos)
            cambios = True

    # 3) bajar los feeds en paralelo
    activos = [c for c in canales if c["id"]]
    with ThreadPoolExecutor(max_workers=HILOS) as pool:
        contenidos = list(pool.map(lambda c: descargar_feed(c["id"]), activos))

    # 4) filtrar
    ya_alertados = set(estado["alertados"])
    memoria = ahora - timedelta(hours=HORAS_MEMORIA_TITULOS)
    titulos_recientes = [t for t in estado["titulos"] if datetime.fromisoformat(t["fecha"]) >= memoria]
    candidatos = []
    for canal, contenido in zip(activos, contenidos):
        if not contenido:
            continue
        for v in videos_de_feed(contenido):
            if v["id"] in ya_alertados or v["publicado"] < limite:
                continue
            if not pasa_filtro(v["titulo"], canal["estricto"]):
                continue
            candidatos.append(v)

    candidatos.sort(key=lambda v: v["publicado"])  # los más antiguos primero
    print(f"Canales activos: {len(activos)} · candidatos nuevos: {len(candidatos)}")

    # 5) enviar
    enviados = 0
    for v in candidatos:
        if enviados >= MAX_ALERTAS_POR_EJECUCION:
            print("Tope por ejecución alcanzado; el resto irá en la siguiente.")
            break
        if es_repetido_de_otro_canal(v, titulos_recientes):
            print(f"  [repetido de otro canal, se omite] {v['canal']}: {v['titulo']}")
            estado["alertados"].append(v["id"])
            cambios = True
            continue
        print(f"Avisando: {v['canal']}: {v['titulo']}")
        if args.dry_run:
            print(texto_alerta(v), "\n")
            ok = True
        else:
            ok = enviar_alerta(v)
            time.sleep(1.2)
        if ok:
            estado["alertados"].append(v["id"])
            registro = {"n": normalizar(v["titulo"]), "canal": v["canal"], "fecha": ahora.isoformat()}
            estado["titulos"].append(registro)
            titulos_recientes.append(registro)
            enviados += 1
            cambios = True
        else:
            print("  [aviso] fallo al enviar; se reintentará en la próxima ejecución")

    if cambios and not args.dry_run:
        guardar_estado(estado)
    print(f"Listo. Alertas enviadas: {enviados}")


if __name__ == "__main__":
    main()
