"""
Monitor de Hechos de Importancia (SMV + BVL)
============================================

Qué hace, en cada ejecución:
  1. Lee la página "Hechos de Importancia del Día" de la SMV (fuente principal,
     publica unos minutos antes que la BVL). Recorre todas sus páginas.
  2. Consulta la API de la BVL (fuente de respaldo) para hoy y ayer. Sirve para
     atrapar lo que la SMV no mostró (por ejemplo, un hecho publicado justo
     antes de medianoche, cuando la página "del día" se reinicia).
  3. Filtra solo las empresas de EMPRESAS (abajo).
  4. Compara contra seen.json para no avisar dos veces lo mismo.
  5. Por cada hecho nuevo envía un correo con los PDFs adjuntos a todos los
     destinatarios de la variable EMAIL_TO.

Variables de entorno (se guardan como "Secrets" en GitHub):
  GMAIL_USER          correo del Gmail robot (remitente)
  GMAIL_APP_PASSWORD  contraseña de aplicación de 16 caracteres de ese Gmail
  EMAIL_TO            destinatarios separados por coma

Modo prueba (TEST_MODE=1): no lee ni modifica seen.json; toma el hecho de
importancia más reciente de Buenaventura en la BVL (últimos 120 días) y lo
envía, para comprobar que el correo y el PDF adjunto llegan bien.
"""

from __future__ import annotations

import json
import os
import re
import smtplib
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path

import requests
from bs4 import BeautifulSoup

# ---------------------------------------------------------------------------
# CONFIGURACIÓN: aquí se agregan o quitan empresas
# ---------------------------------------------------------------------------
# keywords: palabras que deben aparecer en el nombre de la empresa en la SMV
#           (todas, en mayúsculas, sin importar tildes).
# bvl_rpj:  código de la empresa en la BVL (se obtiene de la API de la BVL).
EMPRESAS = [
    {"ticker": "BVN", "nombre": "Buenaventura",
     "keywords": ["BUENAVENTURA"], "bvl_rpj": "B20003"},
    {"ticker": "CVERDEC1", "nombre": "Cerro Verde",
     "keywords": ["CERRO VERDE"], "bvl_rpj": "CM0006"},
    {"ticker": "MINSURI1", "nombre": "Minsur",
     "keywords": ["MINSUR"], "bvl_rpj": "A20032"},
    {"ticker": "SCCO", "nombre": "Southern Copper Corporation",
     "keywords": ["SOUTHERN COPPER"], "bvl_rpj": "B60052"},
    {"ticker": "SPCC", "nombre": "Southern Peru Copper (Sucursal del Perú)",
     "keywords": ["SOUTHERN PERU"], "bvl_rpj": "B20027"},
]

SMV_URL = ("https://www.smv.gob.pe/SIMV/Frm_hechosdeImportanciaDia"
           "?data=38C2EC33FA106691BB5B5039DACFDF50795D8EC3AF")
SMV_GRID = "ctl00$MainContent$grdHechosImportancia2"
BVL_API = "https://dataondemand.bvl.com.pe/v1/corporate-actions"
BVL_DOCS = "https://documents.bvl.com.pe"

STATE_FILE = Path(__file__).with_name("seen.json")
LIMA = timezone(timedelta(hours=-5))          # Perú no usa horario de verano
MAX_ADJUNTOS_MB = 20                          # Gmail acepta hasta 25 MB
VENTANA_DUPLICADO_MIN = 45                    # SMV vs BVL del mismo hecho
HEARTBEAT_DIAS = 25                           # evita que GitHub apague el horario
TIMEOUT = 40

HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                   "AppleWebKit/537.36 (KHTML, like Gecko) "
                   "Chrome/124.0 Safari/537.36"),
    "Accept-Language": "es-PE,es;q=0.9",
}


# ---------------------------------------------------------------------------
# Modelo de datos
# ---------------------------------------------------------------------------
@dataclass
class Hecho:
    fuente: str                 # "SMV" o "BVL"
    empresa_raw: str            # nombre tal como aparece en la fuente
    empresa: dict               # entrada de EMPRESAS
    fecha_hora: datetime        # hora de publicación (Lima)
    tipo: str
    descripcion: str
    documentos: list[str] = field(default_factory=list)   # URLs de los PDFs
    expediente: str = ""

    def doc_ids(self) -> list[str]:
        """Identificadores únicos de cada documento (para deduplicar)."""
        return [f"{self.fuente}:{d}" for d in self.documentos] or \
               [f"{self.fuente}:{self.empresa_raw}:{self.fecha_hora:%Y%m%d%H%M}"]


# ---------------------------------------------------------------------------
# Utilidades
# ---------------------------------------------------------------------------
def ahora_lima() -> datetime:
    return datetime.now(LIMA)


def normalizar(texto: str) -> str:
    tabla = str.maketrans("ÁÉÍÓÚÜÑáéíóúüñ", "AEIOUUNaeiouun")
    return re.sub(r"\s+", " ", texto.translate(tabla)).strip().upper()


def identificar_empresa(nombre: str) -> dict | None:
    n = normalizar(nombre)
    for emp in EMPRESAS:
        if all(normalizar(k) in n for k in emp["keywords"]):
            return emp
    return None


def log(msg: str) -> None:
    print(f"[{ahora_lima():%Y-%m-%d %H:%M:%S}] {msg}", flush=True)


# ---------------------------------------------------------------------------
# Fuente 1: SMV – Hechos de Importancia del Día
# ---------------------------------------------------------------------------
def _campos_formulario(soup: BeautifulSoup) -> dict:
    """Campos ocultos de ASP.NET (VIEWSTATE, etc.) necesarios para pedir la página 2."""
    form = soup.find("form")
    datos = {}
    if not form:
        return datos
    for el in form.find_all("input"):
        nombre, tipo = el.get("name"), (el.get("type") or "text").lower()
        if not nombre or tipo in ("submit", "image", "button"):
            continue
        if tipo in ("radio", "checkbox") and not el.has_attr("checked"):
            continue
        datos[nombre] = el.get("value", "")
    return datos


def _paginas_pendientes(soup: BeautifulSoup) -> list[str]:
    """Devuelve los argumentos 'Page$N' de los enlaces de paginación."""
    return re.findall(r"__doPostBack\('[^']*grdHechosImportancia2','(Page\$\d+)'\)",
                      str(soup))


def parsear_smv(html: str) -> list[Hecho]:
    soup = BeautifulSoup(html, "html.parser")
    hechos: list[Hecho] = []
    for lbl in soup.select("span[id*=lblEmpresahi]"):
        empresa_raw = lbl.get_text(strip=True)
        emp = identificar_empresa(empresa_raw)
        if not emp:
            continue
        fila = lbl.find_parent("tr")
        for card in fila.select("div.card-body"):
            exp_txt = card.select_one("p.text-blue")
            exp_txt = exp_txt.get_text(" ", strip=True) if exp_txt else ""
            tipo = card.select_one("h5.card-title")
            desc = card.select_one("p.card-text")
            # Un expediente antiguo puede "regularizarse" hoy: la tarjeta trae TODOS
            # sus documentos históricos (vimos uno con 203). Solo se consideran
            # los documentos fechados en los últimos 2 días.
            limite = ahora_lima() - timedelta(days=2)
            links, horas = [], []
            for div in card.select("div.archivos-div"):
                a = div.find("a", href=True)
                if not (a and "documento.aspx" in a["href"]):
                    continue
                partes = [d.get_text(strip=True)
                          for d in div.select("div.fecha-adjunto div")]
                fecha_doc = None
                if len(partes) == 2:
                    try:
                        fecha_doc = datetime.strptime(
                            " ".join(partes), "%d/%m/%Y %H:%M").replace(tzinfo=LIMA)
                    except ValueError:
                        pass
                if fecha_doc and fecha_doc < limite:
                    continue
                links.append(a["href"].strip())
                if fecha_doc:
                    horas.append(fecha_doc)
            m = re.search(r"EXP\.\s*(\d+)\s+DEL\s+(\d\d/\d\d/\d{4} \d\d:\d\d)", exp_txt)
            if not links and card.select("div.archivos-div"):
                continue                     # solo tenía documentos antiguos
            fh = max(horas) if horas else (
                datetime.strptime(m.group(2), "%d/%m/%Y %H:%M").replace(tzinfo=LIMA)
                if m else ahora_lima())
            hechos.append(Hecho(
                fuente="SMV", empresa_raw=empresa_raw, empresa=emp, fecha_hora=fh,
                tipo=tipo.get_text(" ", strip=True) if tipo else "",
                descripcion=desc.get_text(" ", strip=True) if desc else "",
                documentos=links, expediente=m.group(1) if m else "",
            ))
    return hechos


def leer_smv(session: requests.Session) -> list[Hecho]:
    r = session.get(SMV_URL, timeout=TIMEOUT)
    r.raise_for_status()
    if "lblEmpresahi" not in r.text and "Hechos de Importancia del D" not in r.text:
        raise RuntimeError("La SMV no devolvió la página esperada "
                           "(¿cambió el enlace o hay un bloqueo?)")
    html_paginas = [r.text]
    soup = BeautifulSoup(r.text, "html.parser")
    vistas = {"Page$1"}
    pendientes = [p for p in _paginas_pendientes(soup) if p not in vistas]
    while pendientes:                       # recorre página 2, 3, ...
        pagina = pendientes.pop(0)
        if pagina in vistas:
            continue
        datos = _campos_formulario(soup)
        datos["__EVENTTARGET"] = SMV_GRID
        datos["__EVENTARGUMENT"] = pagina
        r = session.post(SMV_URL, data=datos, timeout=TIMEOUT,
                         headers={"Referer": SMV_URL})
        r.raise_for_status()
        vistas.add(pagina)
        html_paginas.append(r.text)
        soup = BeautifulSoup(r.text, "html.parser")
        pendientes += [p for p in _paginas_pendientes(soup)
                       if p not in vistas and p not in pendientes]
        if len(vistas) > 15:                # protección contra bucles
            break
    hechos = []
    for html in html_paginas:
        hechos += parsear_smv(html)
    log(f"SMV: {len(html_paginas)} página(s) leída(s), "
        f"{len(hechos)} hecho(s) de empresas seguidas")
    return hechos


# ---------------------------------------------------------------------------
# Fuente 2: BVL – API de hechos de importancia (respaldo)
# ---------------------------------------------------------------------------
def parsear_bvl(data: dict) -> list[Hecho]:
    por_rpj = {e["bvl_rpj"]: e for e in EMPRESAS}
    hechos = []
    for it in data.get("content", []):
        emp = por_rpj.get(it.get("rpjCode"))
        if not emp:
            continue
        fh = datetime.strptime(it["registerDate"][:19], "%Y-%m-%d %H:%M:%S").replace(tzinfo=LIMA)
        tipos = "; ".join(c.get("descCodeHHII", "") for c in it.get("codes", []))
        docs = [BVL_DOCS + d["path"] for d in it.get("documents", []) if d.get("path")]
        obs = (it.get("observation") or "").strip()
        hechos.append(Hecho(fuente="BVL", empresa_raw=it.get("businessName", ""),
                            empresa=emp, fecha_hora=fh, tipo=tipos,
                            descripcion=obs, documentos=docs))
    return hechos


def consultar_bvl(session: requests.Session, desde: str, hasta: str,
                  rpj: str = "", size: int = 300) -> dict:
    cuerpo = {"rpjCode": rpj, "subIFCode": "", "startDate": desde,
              "endDate": hasta, "search": "", "page": 1, "size": size}
    r = session.post(BVL_API, json=cuerpo, timeout=TIMEOUT, headers={
        "Origin": "https://www.bvl.com.pe",
        "Referer": "https://www.bvl.com.pe/"})
    r.raise_for_status()
    return r.json()


def leer_bvl(session: requests.Session) -> list[Hecho]:
    hoy = ahora_lima().date()
    data = consultar_bvl(session, f"{hoy - timedelta(days=1)}", f"{hoy}")
    hechos = parsear_bvl(data)
    log(f"BVL: {data.get('totalElements', '?')} hecho(s) en total, "
        f"{len(hechos)} de empresas seguidas")
    return hechos


# ---------------------------------------------------------------------------
# Estado (qué ya se avisó)
# ---------------------------------------------------------------------------
def cargar_estado() -> dict | None:
    if not STATE_FILE.exists():
        return None
    return json.loads(STATE_FILE.read_text(encoding="utf-8"))


def guardar_estado(estado: dict) -> None:
    # Conserva solo lo de los últimos 40 días para que el archivo no crezca.
    limite = (ahora_lima() - timedelta(days=40)).isoformat()
    estado["vistos"] = {k: v for k, v in estado["vistos"].items() if v["t"] >= limite}
    STATE_FILE.write_text(json.dumps(estado, ensure_ascii=False, indent=1,
                                     sort_keys=True), encoding="utf-8")


def es_duplicado_entre_fuentes(h: Hecho, estado: dict) -> bool:
    """¿Un hecho de la BVL ya fue avisado desde la SMV (misma empresa, hora cercana)?"""
    if h.fuente != "BVL":
        return False
    for v in estado["vistos"].values():
        if v.get("fuente") != "SMV" or v.get("ticker") != h.empresa["ticker"]:
            continue
        t_smv = datetime.fromisoformat(v["t"])
        if timedelta(0) <= h.fecha_hora - t_smv <= timedelta(minutes=VENTANA_DUPLICADO_MIN):
            return True
    return False


def registrar(h: Hecho, estado: dict) -> None:
    for d in h.doc_ids():
        estado["vistos"][d] = {"t": h.fecha_hora.isoformat(), "fuente": h.fuente,
                               "ticker": h.empresa["ticker"]}


# ---------------------------------------------------------------------------
# Correo
# ---------------------------------------------------------------------------
def descargar_pdfs(session: requests.Session, h: Hecho) -> list[tuple[str, bytes]]:
    adjuntos, total = [], 0
    for i, url in enumerate(h.documentos, 1):
        try:
            r = session.get(url, timeout=TIMEOUT)
            r.raise_for_status()
        except Exception as e:                         # el link igual va en el cuerpo
            log(f"  No se pudo descargar {url}: {e}")
            continue
        contenido = r.content
        if not contenido.startswith(b"%PDF"):
            log(f"  {url} no es un PDF; se omite como adjunto")
            continue
        total += len(contenido)
        if total > MAX_ADJUNTOS_MB * 1024 * 1024:
            log("  Límite de tamaño alcanzado; el resto va solo como link")
            break
        nombre = (f"{h.empresa['ticker']}_{h.fecha_hora:%Y-%m-%d_%H%M}"
                  f"{'_' + str(i) if len(h.documentos) > 1 else ''}.pdf")
        adjuntos.append((nombre, contenido))
    return adjuntos


def construir_correo(h: Hecho, adjuntos: list[tuple[str, bytes]],
                     remitente: str, destinatarios: list[str],
                     prueba: bool = False) -> EmailMessage:
    tipo_corto = re.sub(r"^\d+\.\s*", "", h.tipo).strip().capitalize()[:70]
    asunto = (f"{'[PRUEBA] ' if prueba else ''}[HI] {h.empresa['ticker']} – "
              f"{tipo_corto} – {h.fecha_hora:%d/%m %H:%M}")
    links_txt = "\n".join(f"  - {u}" for u in h.documentos) or "  (sin documentos)"
    texto = (
        f"{h.empresa['nombre']} publicó un hecho de importancia.\n\n"
        f"Empresa:      {h.empresa_raw}\n"
        f"Tipo:         {h.tipo}\n"
        f"Publicado:    {h.fecha_hora:%d/%m/%Y %H:%M} (hora de Lima)\n"
        f"Fuente:       {h.fuente}{'  |  Expediente ' + h.expediente if h.expediente else ''}\n\n"
        f"Descripción:\n{h.descripcion or '(sin descripción)'}\n\n"
        f"Documentos ({len(adjuntos)} adjunto(s)):\n{links_txt}\n\n"
        f"—\nAviso automático del monitor de hechos de importancia.\n"
        f"Detectado: {ahora_lima():%d/%m/%Y %H:%M:%S}\n"
    )
    msg = EmailMessage()
    msg["Subject"] = asunto
    msg["From"] = f"Monitor Hechos de Importancia <{remitente}>"
    msg["To"] = ", ".join(destinatarios)
    msg.set_content(texto)
    for nombre, contenido in adjuntos:
        msg.add_attachment(contenido, maintype="application", subtype="pdf",
                           filename=nombre)
    return msg


def enviar(msg: EmailMessage, usuario: str, clave: str) -> None:
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=60) as s:
        s.login(usuario, clave)
        s.send_message(msg)


def credenciales() -> tuple[str, str, list[str]]:
    usuario = os.environ.get("GMAIL_USER", "").strip()
    clave = os.environ.get("GMAIL_APP_PASSWORD", "").replace(" ", "").strip()
    destinos = [d.strip() for d in os.environ.get("EMAIL_TO", "").split(",") if d.strip()]
    faltan = [n for n, v in (("GMAIL_USER", usuario), ("GMAIL_APP_PASSWORD", clave),
                             ("EMAIL_TO", destinos)) if not v]
    if faltan:
        sys.exit(f"Faltan los Secrets: {', '.join(faltan)}")
    return usuario, clave, destinos


# ---------------------------------------------------------------------------
# Programa principal
# ---------------------------------------------------------------------------
def modo_prueba(session: requests.Session) -> None:
    usuario, clave, destinos = credenciales()
    hoy = ahora_lima().date()
    data = consultar_bvl(session, f"{hoy - timedelta(days=120)}", f"{hoy}",
                         rpj=EMPRESAS[0]["bvl_rpj"], size=5)
    hechos = parsear_bvl(data)
    if not hechos:
        sys.exit("No se encontró ningún hecho reciente para la prueba")
    h = hechos[0]
    adj = descargar_pdfs(session, h)
    enviar(construir_correo(h, adj, usuario, destinos, prueba=True), usuario, clave)
    log(f"Correo de PRUEBA enviado a {len(destinos)} destinatario(s) "
        f"con {len(adj)} adjunto(s): {h.empresa['ticker']} {h.fecha_hora:%d/%m %H:%M}")


def main() -> int:
    session = requests.Session()
    session.headers.update(HEADERS)

    if os.environ.get("TEST_MODE") == "1":
        modo_prueba(session)
        return 0

    estado = cargar_estado()
    primera_vez = estado is None
    if primera_vez:
        estado = {"vistos": {}, "heartbeat": ahora_lima().isoformat()}

    hechos, errores = [], []
    for nombre, lector in (("SMV", leer_smv), ("BVL", leer_bvl)):
        try:
            hechos += lector(session)
        except Exception as e:
            errores.append(f"{nombre}: {e}")
            log(f"ERROR leyendo {nombre}: {e}")

    if len(errores) == 2:
        # Ninguna fuente respondió: falla la ejecución para que GitHub lo marque
        # en rojo (y te avise por correo si fallan varias seguidas).
        log("Ninguna fuente respondió.")
        return 1

    # SMV primero: es la fuente más rápida y la que manda en la deduplicación.
    hechos.sort(key=lambda h: (h.fuente != "SMV", h.fecha_hora))
    nuevos = []
    for h in hechos:
        if h.documentos:
            # Solo los documentos que aún no se avisaron (cubre el caso de un
            # documento nuevo agregado a un expediente que ya conocíamos).
            pendientes = [u for u in h.documentos
                          if f"{h.fuente}:{u}" not in estado["vistos"]]
            if not pendientes:
                continue
            h.documentos = pendientes
        elif any(d in estado["vistos"] for d in h.doc_ids()):
            continue
        if es_duplicado_entre_fuentes(h, estado):
            registrar(h, estado)
            continue
        registrar(h, estado)
        nuevos.append(h)

    if primera_vez:
        log(f"Primera ejecución: se registraron {len(nuevos)} hecho(s) ya existentes "
            "sin enviar correos. Desde ahora solo se avisarán los nuevos.")
        guardar_estado(estado)
        return 0

    fallidos = 0
    if nuevos:
        usuario, clave, destinos = credenciales()
        for h in nuevos:
            try:
                adj = descargar_pdfs(session, h)
                enviar(construir_correo(h, adj, usuario, destinos), usuario, clave)
                log(f"ENVIADO: {h.empresa['ticker']} {h.fecha_hora:%d/%m %H:%M} "
                    f"({h.fuente}, {len(adj)} adjunto(s))")
            except Exception as e:
                # No se marca como visto: se reintenta en la próxima revisión.
                fallidos += 1
                for d in h.doc_ids():
                    estado["vistos"].pop(d, None)
                log(f"ERROR enviando {h.empresa['ticker']} {h.fecha_hora:%d/%m %H:%M}: {e}")
            time.sleep(1)
    else:
        log("Sin hechos nuevos.")

    # "Latido": actualiza el archivo cada ~25 días aunque no haya novedades,
    # porque GitHub desactiva los horarios de repos públicos sin actividad en 60 días.
    ultimo = datetime.fromisoformat(estado.get("heartbeat", "2000-01-01T00:00:00-05:00"))
    if nuevos or ahora_lima() - ultimo > timedelta(days=HEARTBEAT_DIAS):
        estado["heartbeat"] = ahora_lima().isoformat()
        guardar_estado(estado)
    return 1 if fallidos else 0


if __name__ == "__main__":
    sys.exit(main())
