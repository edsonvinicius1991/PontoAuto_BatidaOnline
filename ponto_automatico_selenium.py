#!/usr/bin/env python3
"""
Ponto Automático - Ahgora (Selenium + Edge + UI)
Realiza 4 batidas diárias com variação natural de horários,
totalizando entre 8h00m e 8h05m trabalhadas.

Dependências:
    pip install selenium webdriver-manager
Opcional (esconder na bandeja do sistema):
    pip install pystray pillow
"""

import os
import importlib
import json
import random
import re
import shutil
import subprocess
import threading
import time
import traceback
import tkinter as tk
from tkinter import messagebox
from datetime import datetime, timedelta
from pathlib import Path
from queue import Empty, Queue
import ctypes
from ctypes import wintypes

from selenium import webdriver
from selenium.common.exceptions import SessionNotCreatedException
from selenium.webdriver.common.by import By
from selenium.webdriver.edge.options import Options
from selenium.webdriver.edge.service import Service
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait
from webdriver_manager.microsoft import EdgeChromiumDriverManager

pystray = None
Image = None
ImageDraw = None

# --- Configuração -------------------------------------------------------------
URL = "https://www.ahgora.com.br/novabatidaonline/?defaultDevice=a774091"
CONFIG_FILE = Path(__file__).with_name("ponto_config.json")
LOGO_PNG = Path(__file__).with_name("assets") / "logo_ponto_auto.png"
LOGO_ICO = Path(__file__).with_name("assets") / "logo_ponto_auto.ico"
APP_ID = "petrobras.pontoauto.desktop"

# Faixa de variação (minutos) em relação ao horário base
OFFSETS = {
    "entrada": (-5, 3),        # 07:55 ~ 08:03
    "saida_almoco": (-2, 6),   # 11:58 ~ 12:06
    "retorno_almoco": (1, 8),  # 13:01 ~ 13:08
}
MAX_EXTRA_MIN = 5   # minutos extras além das 8h exatas (0 a 5)
MAX_RETRIES = 3     # tentativas em caso de falha
TIMEOUT = 15        # segundos de espera para elementos na página

ICONS = ["🟢", "🟡", "🔵", "🔴"]

UI_COLORS = {
    "bg": "#0b1220",
    "card": "#141e30",
    "card_alt": "#101826",
    "text": "#e5e7eb",
    "muted": "#94a3b8",
    "accent": "#00c2a8",
    "accent_hover": "#00ad96",
    "danger": "#d64545",
    "warning": "#2b3a55",
    "log_bg": "#0a101b",
}


if os.name == "nt":
    class _NotifyIconData(ctypes.Structure):
        _fields_ = [
            ("cbSize", wintypes.DWORD),
            ("hWnd", wintypes.HWND),
            ("uID", wintypes.UINT),
            ("uFlags", wintypes.UINT),
            ("uCallbackMessage", wintypes.UINT),
            ("hIcon", wintypes.HICON),
            ("szTip", wintypes.WCHAR * 128),
            ("dwState", wintypes.DWORD),
            ("dwStateMask", wintypes.DWORD),
            ("szInfo", wintypes.WCHAR * 256),
            ("uTimeoutOrVersion", wintypes.UINT),
            ("szInfoTitle", wintypes.WCHAR * 64),
            ("dwInfoFlags", wintypes.DWORD),
            ("guidItem", ctypes.c_byte * 16),
            ("hBalloonIcon", wintypes.HICON),
        ]


class NativeTrayManager:
    """Gerencia ícone de bandeja nativo do Windows sem dependências externas."""

    NIM_ADD = 0x00000000
    NIM_DELETE = 0x00000002
    NIF_MESSAGE = 0x00000001
    NIF_ICON = 0x00000002
    NIF_TIP = 0x00000004

    WM_APP = 0x8000
    WM_NULL = 0x0000
    WM_LBUTTONUP = 0x0202
    WM_LBUTTONDBLCLK = 0x0203
    WM_RBUTTONUP = 0x0205
    TPM_LEFTALIGN = 0x0000
    TPM_BOTTOMALIGN = 0x0020
    TPM_RIGHTBUTTON = 0x0002
    TPM_RETURNCMD = 0x0100
    MF_STRING = 0x0000

    GWLP_WNDPROC = -4
    IDI_APPLICATION = 32512
    IMAGE_ICON = 1
    LR_LOADFROMFILE = 0x0010
    LR_DEFAULTSIZE = 0x0040
    TRAY_UID = 1
    CMD_SHOW = 1001
    CMD_EXIT = 1002

    def __init__(self, root: tk.Tk, on_restore, on_exit, log=print, icon_path: Path | None = None):
        self.root = root
        self.on_restore = on_restore
        self.on_exit = on_exit
        self.log = log
        self.icon_path = icon_path
        self.available = os.name == "nt"
        self.active = False
        self._hwnd = None
        self._tray_msg = self.WM_APP + 1
        self._old_wndproc = None
        self._wndproc_ref = None
        self._nid = None
        self._menu = None

        self._user32 = ctypes.windll.user32 if self.available else None
        self._shell32 = ctypes.windll.shell32 if self.available else None

        if self.available:
            is_64 = ctypes.sizeof(ctypes.c_void_p) == 8
            lresult_t = ctypes.c_longlong if is_64 else ctypes.c_long
            self._user32.CallWindowProcW.argtypes = [
                ctypes.c_void_p,
                wintypes.HWND,
                wintypes.UINT,
                wintypes.WPARAM,
                wintypes.LPARAM,
            ]
            self._user32.CallWindowProcW.restype = lresult_t

    def start(self) -> bool:
        if not self.available:
            return False

        if self.active:
            return True

        try:
            self.root.update_idletasks()
            self._hwnd = self.root.winfo_id()
            if not self._hwnd:
                return False

            if not self._install_wndproc(self._hwnd):
                return False

            nid = _NotifyIconData()
            nid.cbSize = ctypes.sizeof(_NotifyIconData)
            nid.hWnd = self._hwnd
            nid.uID = self.TRAY_UID
            nid.uFlags = self.NIF_MESSAGE | self.NIF_ICON | self.NIF_TIP
            nid.uCallbackMessage = self._tray_msg
            nid.hIcon = self._load_icon_handle()
            nid.szTip = "Ponto Automático"

            if not self._shell32.Shell_NotifyIconW(self.NIM_ADD, ctypes.byref(nid)):
                self._uninstall_wndproc()
                return False

            self._nid = nid
            self.active = True
            self._menu = self._create_menu()
            return True
        except Exception as err:
            self.log(f"⚠️ Falha ao ativar bandeja nativa: {err}")
            self._uninstall_wndproc()
            return False

    def stop(self) -> None:
        if not self.available:
            return

        try:
            if self.active and self._nid is not None:
                self._shell32.Shell_NotifyIconW(self.NIM_DELETE, ctypes.byref(self._nid))
        except Exception:
            pass
        finally:
            self.active = False
            self._nid = None
            if self._menu:
                try:
                    self._user32.DestroyMenu(self._menu)
                except Exception:
                    pass
                self._menu = None
            self._uninstall_wndproc()

    def _create_menu(self):
        menu = self._user32.CreatePopupMenu()
        if not menu:
            return None

        self._user32.AppendMenuW(menu, self.MF_STRING, self.CMD_SHOW, "Reexibir")
        self._user32.AppendMenuW(menu, self.MF_STRING, self.CMD_EXIT, "Fechar")
        return menu

    def _load_icon_handle(self):
        if self.icon_path and self.icon_path.exists():
            try:
                hicon = self._user32.LoadImageW(
                    0,
                    str(self.icon_path),
                    self.IMAGE_ICON,
                    0,
                    0,
                    self.LR_LOADFROMFILE | self.LR_DEFAULTSIZE,
                )
                if hicon:
                    return hicon
            except Exception:
                pass

        return self._user32.LoadIconW(0, self.IDI_APPLICATION)

    def _show_context_menu(self):
        if not self._menu:
            return

        pt = wintypes.POINT()
        self._user32.GetCursorPos(ctypes.byref(pt))
        self._user32.SetForegroundWindow(self._hwnd)
        cmd = self._user32.TrackPopupMenu(
            self._menu,
            self.TPM_LEFTALIGN | self.TPM_BOTTOMALIGN | self.TPM_RIGHTBUTTON | self.TPM_RETURNCMD,
            pt.x,
            pt.y,
            0,
            self._hwnd,
            None,
        )
        self._user32.PostMessageW(self._hwnd, self.WM_NULL, 0, 0)

        if cmd == self.CMD_SHOW:
            self.root.after(0, self.on_restore)
        elif cmd == self.CMD_EXIT:
            self.root.after(0, self.on_exit)

    def _install_wndproc(self, hwnd: int) -> bool:
        is_64 = ctypes.sizeof(ctypes.c_void_p) == 8
        lresult_t = ctypes.c_longlong if is_64 else ctypes.c_long
        wndproc_type = ctypes.WINFUNCTYPE(lresult_t, wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM)
        self._wndproc_ref = wndproc_type(self._wndproc)

        if is_64:
            set_wndproc = self._user32.SetWindowLongPtrW
            set_wndproc.restype = ctypes.c_void_p
        else:
            set_wndproc = self._user32.SetWindowLongW
            set_wndproc.restype = ctypes.c_void_p

        set_wndproc.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_void_p]
        old = set_wndproc(hwnd, self.GWLP_WNDPROC, self._wndproc_ref)
        if not old:
            self._wndproc_ref = None
            return False

        self._old_wndproc = ctypes.c_void_p(old)
        return True

    def _uninstall_wndproc(self) -> None:
        if not self.available or not self._hwnd or not self._old_wndproc:
            return

        try:
            if ctypes.sizeof(ctypes.c_void_p) == 8:
                set_wndproc = self._user32.SetWindowLongPtrW
            else:
                set_wndproc = self._user32.SetWindowLongW
            set_wndproc.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_void_p]
            set_wndproc(self._hwnd, self.GWLP_WNDPROC, self._old_wndproc)
        except Exception:
            pass
        finally:
            self._old_wndproc = None
            self._wndproc_ref = None

    def _wndproc(self, hwnd, msg, wparam, lparam):
        try:
            if msg == self._tray_msg and int(wparam) == self.TRAY_UID:
                if int(lparam) in (self.WM_LBUTTONUP, self.WM_LBUTTONDBLCLK):
                    self.root.after(0, self.on_restore)
                    return 0
                if int(lparam) == self.WM_RBUTTONUP:
                    self._show_context_menu()
                    return 0

            return self._call_window_proc(hwnd, msg, wparam, lparam)
        except Exception as err:
            self.log(f"⚠️ Erro no callback da bandeja: {err}")
            return 0

    def _call_window_proc(self, hwnd, msg, wparam, lparam):
        if not self._old_wndproc:
            return 0

        bits = ctypes.sizeof(ctypes.c_void_p) * 8
        mask = (1 << bits) - 1
        wparam_norm = int(wparam) & mask
        lparam_norm = int(lparam) & mask

        if bits == 64 and lparam_norm >= (1 << 63):
            lparam_norm -= (1 << 64)
        if bits == 32 and lparam_norm >= (1 << 31):
            lparam_norm -= (1 << 32)

        return self._user32.CallWindowProcW(
            ctypes.c_void_p(self._old_wndproc.value),
            wintypes.HWND(hwnd),
            wintypes.UINT(msg),
            wintypes.WPARAM(wparam_norm),
            wintypes.LPARAM(lparam_norm),
        )


def carregar_config() -> dict[str, str | bool]:
    config = {
        "employee_id": "",
        "password": "",
        "save_credentials": False,
    }

    if not CONFIG_FILE.exists():
        return config

    try:
        data = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
    except Exception:
        return config

    config["employee_id"] = str(data.get("employee_id", ""))
    config["password"] = str(data.get("password", ""))
    config["save_credentials"] = bool(data.get("save_credentials", False))
    return config


def salvar_config(employee_id: str, password: str, save_credentials: bool) -> None:
    payload = {
        "employee_id": employee_id if save_credentials else "",
        "password": password if save_credentials else "",
        "save_credentials": bool(save_credentials),
    }
    CONFIG_FILE.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def carregar_dependencias_bandeja(log=print) -> bool:
    global pystray, Image, ImageDraw

    try:
        pystray = importlib.import_module("pystray")
        pil_image = importlib.import_module("PIL.Image")
        pil_draw = importlib.import_module("PIL.ImageDraw")
        Image = pil_image
        ImageDraw = pil_draw
        return True
    except Exception as err:
        log(
            "ℹ️ Bandeja do sistema opcional indisponível "
            f"({err}). Usando modo nativo: minimizar para a barra de tarefas."
        )
        return False


def _icone(idx: int) -> str:
    return ICONS[idx - 1] if 1 <= idx <= len(ICONS) else "⚪"


# --- Geração de horários ------------------------------------------------------
def gerar_horarios() -> list[tuple[datetime, str]]:
    """Gera 4 horários com variação aleatória garantindo 8h~8h05 trabalhadas."""
    hoje = datetime.now().replace(second=0, microsecond=0)

    def base(h: int, m: int, faixa: tuple[int, int]) -> datetime:
        return hoje.replace(hour=h, minute=m) + timedelta(minutes=random.randint(*faixa))

    entrada = base(8, 0, OFFSETS["entrada"])
    saida_almoco = base(12, 0, OFFSETS["saida_almoco"])
    retorno_almoco = base(13, 0, OFFSETS["retorno_almoco"])

    # Saída = entrada + trabalho_total + intervalo_almoço
    almoco_min = (retorno_almoco - saida_almoco).total_seconds() / 60
    trabalho_total = 480 + random.randint(0, MAX_EXTRA_MIN)
    saida_min = entrada.hour * 60 + entrada.minute + trabalho_total + almoco_min
    saida = hoje.replace(hour=int(saida_min // 60), minute=int(saida_min % 60))

    return [
        (entrada, "Entrada"),
        (saida_almoco, "Saída Almoço"),
        (retorno_almoco, "Retorno Almoço"),
        (saida, "Saída"),
    ]


def exibir_horarios(pontos: list[tuple[datetime, str]], log=print) -> None:
    t0, t1, t2, t3 = [p[0] for p in pontos]
    total = (t1 - t0) + (t3 - t2)
    th, tm = divmod(int(total.total_seconds() / 60), 60)

    log(f"\n{'═' * 50}")
    log(f"  🕐  PONTO AUTOMÁTICO  ·  {datetime.now():%d/%m/%Y}")
    log(f"{'═' * 50}")
    for i, (t, nome) in enumerate(pontos):
        log(f"  {ICONS[i]}  {nome:<22}  {t:%H:%M}")
    log("─" * 50)
    log(f"  ⏱️   Total de trabalho: {th}h{tm:02d}m")
    log(f"{'═' * 50}\n")


# --- Inicializa o Edge --------------------------------------------------------
def encontrar_edgedriver_local() -> str | None:
    def obter_major_versao_edge() -> int | None:
        edge_paths = [
            Path(r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe"),
            Path(r"C:\Program Files\Microsoft\Edge\Application\msedge.exe"),
        ]
        for edge_path in edge_paths:
            if not edge_path.exists():
                continue
            try:
                saida = subprocess.check_output(
                    [str(edge_path), "--version"],
                    stderr=subprocess.STDOUT,
                    text=True,
                    timeout=3,
                )
            except Exception:
                continue

            match = re.search(r"(\d+)\.(\d+)\.(\d+)\.(\d+)", saida)
            if match:
                return int(match.group(1))
        return None

    def obter_versao_driver(driver_path: Path) -> tuple[int, int, int, int] | None:
        try:
            saida = subprocess.check_output(
                [str(driver_path), "--version"],
                stderr=subprocess.STDOUT,
                text=True,
                timeout=3,
            )
        except Exception:
            return None

        match = re.search(r"(\d+)\.(\d+)\.(\d+)\.(\d+)", saida)
        if match:
            return tuple(int(match.group(i)) for i in range(1, 5))
        return None

    candidatos: list[Path] = []

    env_driver = os.getenv("SE_EDGEDRIVER")
    if env_driver:
        candidatos.append(Path(env_driver))

    driver_no_path = shutil.which("msedgedriver")
    if driver_no_path:
        candidatos.append(Path(driver_no_path))

    candidatos.extend([
        Path(r"C:\drivers\msedgedriver.exe"),
        Path(r"C:\WebDriver\bin\msedgedriver.exe"),
        Path.home() / "drivers" / "msedgedriver.exe",
    ])

    wdm_root = Path.home() / ".wdm"
    if wdm_root.exists():
        candidatos.extend(wdm_root.rglob("msedgedriver.exe"))

    selenium_cache = Path.home() / ".cache" / "selenium"
    if selenium_cache.exists():
        candidatos.extend(selenium_cache.rglob("msedgedriver.exe"))

    downloads = Path.home() / "Downloads"
    if downloads.exists():
        candidatos.extend(downloads.rglob("msedgedriver.exe"))

    vistos = set()
    encontrados_validos: list[Path] = []
    for caminho in candidatos:
        try:
            caminho = Path(caminho).expanduser().resolve()
        except Exception:
            continue

        caminho_key = str(caminho).lower()
        if caminho_key in vistos:
            continue
        vistos.add(caminho_key)

        if caminho.exists() and caminho.is_file():
            encontrados_validos.append(caminho)

    if not encontrados_validos:
        return None

    edge_major = obter_major_versao_edge()
    if edge_major is not None:
        for caminho in encontrados_validos:
            versao_driver = obter_versao_driver(caminho)
            driver_major = versao_driver[0] if versao_driver else None
            if driver_major == edge_major:
                return str(caminho)

    melhor_caminho = encontrados_validos[0]
    melhor_versao = obter_versao_driver(melhor_caminho) or (0, 0, 0, 0)

    for caminho in encontrados_validos[1:]:
        versao = obter_versao_driver(caminho) or (0, 0, 0, 0)
        if versao > melhor_versao:
            melhor_caminho = caminho
            melhor_versao = versao

    return str(melhor_caminho)


def criar_driver() -> webdriver.Edge:
    options = Options()
    options.add_argument("--start-maximized")
    options.add_argument("--disable-notifications")

    driver_path = encontrar_edgedriver_local()

    if driver_path:
        print(f"✅ Usando EdgeDriver local: {driver_path}")
        service = Service(executable_path=driver_path)
        try:
            return webdriver.Edge(service=service, options=options)
        except SessionNotCreatedException as err:
            raise RuntimeError(
                "EdgeDriver local incompatível com a versão do navegador. "
                "Atualize o msedgedriver para a mesma versão principal do Edge."
            ) from err

    print("⚠️ EdgeDriver local não encontrado. Tentando baixar com webdriver_manager...")
    try:
        driver_path = EdgeChromiumDriverManager().install()
    except Exception as err:
        raise RuntimeError(
            "Não foi possível obter o EdgeDriver automaticamente. "
            "Verifique sua conexão com a internet ou configure um driver local em "
            "SE_EDGEDRIVER (ou no PATH como 'msedgedriver')."
        ) from err

    print(f"⬇️ EdgeDriver baixado em: {driver_path}")
    service = Service(executable_path=driver_path)
    return webdriver.Edge(service=service, options=options)


# --- Registro de ponto --------------------------------------------------------
def registrar_ponto(driver: webdriver.Edge, employee_id: str, password: str) -> None:
    """Executa o fluxo completo de registro de ponto no Ahgora."""
    wait = WebDriverWait(driver, TIMEOUT)

    driver.get(URL)
    time.sleep(2)

    btn_registrar = wait.until(
        EC.element_to_be_clickable((By.XPATH, "//button[contains(., 'Registre seu ponto')]"))
    )
    btn_registrar.click()
    time.sleep(1.5)

    campo_matricula = wait.until(EC.element_to_be_clickable((By.ID, "outlined-basic-account")))
    campo_matricula.click()
    campo_matricula.clear()
    campo_matricula.send_keys(employee_id)
    time.sleep(0.5)

    campo_senha = wait.until(EC.element_to_be_clickable((By.ID, "outlined-basic-password")))
    campo_senha.click()
    campo_senha.clear()
    campo_senha.send_keys(password)
    time.sleep(0.5)

    btn_avancar = wait.until(
        EC.element_to_be_clickable(
            (By.XPATH, "//span[normalize-space()='Avançar'] | //button[.//span[normalize-space()='Avançar']]")
        )
    )
    btn_avancar.click()
    time.sleep(2.5)

    btn_confirmar = wait.until(
        EC.element_to_be_clickable((By.XPATH, "//button[contains(., 'Registrar ponto')]"))
    )

    driver.execute_script("arguments[0].scrollIntoView(true);", btn_confirmar)
    time.sleep(0.5)

    try:
        btn_confirmar.click()
    except Exception:
        driver.execute_script("arguments[0].click();", btn_confirmar)

    time.sleep(2.5)


def _aguardar_ate_horario(
    horario: datetime,
    nome: str,
    idx: int,
    log=print,
    pausa_evento: threading.Event | None = None,
    parar_evento: threading.Event | None = None,
    status_callback=None,
) -> bool:
    """Aguarda o horário alvo. Retorna False se o processamento for cancelado."""
    agora = datetime.now()
    espera = (horario - agora).total_seconds()

    if espera > 0:
        h, rem = divmod(int(espera), 3600)
        m, s = divmod(rem, 60)
        log(f"⏳ [{idx}/4] {_icone(idx)} {nome}")
        log(f"       Horário: {horario:%H:%M}  |  Faltam: {h:02d}h{m:02d}m{s:02d}s")
        if status_callback:
            status_callback(f"{_icone(idx)} {nome} em {h:02d}:{m:02d}:{s:02d}")

    while True:
        if parar_evento and parar_evento.is_set():
            return False

        while pausa_evento and pausa_evento.is_set():
            if status_callback:
                status_callback("⏸️ Execução pausada")
            if parar_evento and parar_evento.is_set():
                return False
            time.sleep(0.5)

        restante = (horario - datetime.now()).total_seconds()
        if restante <= 0:
            if status_callback:
                status_callback(f"⏰ {nome}: executando...")
            return True

        h2, rem2 = divmod(int(restante), 3600)
        m2, s2 = divmod(rem2, 60)
        if status_callback:
            status_callback(f"{_icone(idx)} {nome} em {h2:02d}:{m2:02d}:{s2:02d}")
        time.sleep(1)


def executar_batida_com_navegador(
    nome: str,
    idx: int,
    employee_id: str,
    password: str,
    log=print,
) -> bool:
    """Abre e fecha o navegador em cada batida, com retry em caso de falha."""
    agora_str = datetime.now().strftime("%H:%M:%S")
    log(f"🔔 [{idx}/4] Registrando {nome} às {agora_str}...")

    for tentativa in range(1, MAX_RETRIES + 1):
        driver: webdriver.Edge | None = None
        try:
            driver = criar_driver()
            registrar_ponto(driver, employee_id, password)
            log("   ✅ Batida registrada com sucesso!")
            return True
        except Exception as err:
            if tentativa < MAX_RETRIES:
                log(f"   ⚠️ Tentativa {tentativa} falhou: {err}")
                log("       Repetindo em 15s...")
                time.sleep(15)
            else:
                log(f"   ❌ Falha após {MAX_RETRIES} tentativas: {err}")
                return False
        finally:
            if driver is not None:
                try:
                    driver.quit()
                    log("   🧹 Navegador fechado.")
                except Exception:
                    log("   ⚠️ Não foi possível fechar o navegador com segurança.")


def aguardar_e_bater(
    driver: webdriver.Edge,
    horario: datetime,
    nome: str,
    idx: int,
    employee_id: str,
    password: str,
) -> None:
    """Compatibilidade com script de teste legado."""
    _aguardar_ate_horario(horario, nome, idx)
    registrar_ponto(driver, employee_id, password)


class PontoController:
    def __init__(self, log_callback, status_callback=None):
        self.log = log_callback
        self.status = status_callback or (lambda _msg: None)
        self.thread: threading.Thread | None = None
        self.parar_evento = threading.Event()
        self.pausa_evento = threading.Event()
        self.ativo = False
        self.employee_id = ""
        self.password = ""

    def iniciar(self, employee_id: str, password: str) -> None:
        if self.ativo:
            self.log("ℹ️ Agendamento já está em execução.")
            return

        if not employee_id or not password:
            self.log("⚠️ Informe matrícula e senha antes de iniciar.")
            return

        self.employee_id = employee_id
        self.password = password

        self.parar_evento.clear()
        self.pausa_evento.clear()
        self.thread = threading.Thread(target=self._executar, daemon=True)
        self.ativo = True
        self.thread.start()
        self.log("▶️ Agendamento iniciado.")
        self.status("🟢 Agendamento ativo")

    def pausar_ou_retornar(self) -> bool:
        if not self.ativo:
            self.log("ℹ️ Nenhuma execução ativa para pausar.")
            return False

        if self.pausa_evento.is_set():
            self.pausa_evento.clear()
            self.log("▶️ Execução retomada.")
            return False

        self.pausa_evento.set()
        self.log("⏸️ Execução pausada.")
        return True

    def encerrar(self) -> None:
        self.parar_evento.set()
        self.pausa_evento.clear()
        self.log("⏹️ Encerrando agendamento...")
        self.status("⏹️ Encerrando...")

    def _executar(self) -> None:
        try:
            if not self.employee_id or not self.password:
                self.log("⚠️ Credenciais não configuradas.")
                return

            pontos = gerar_horarios()
            exibir_horarios(pontos, log=self.log)

            agora = datetime.now()
            proximos = [(t, n, i + 1) for i, (t, n) in enumerate(pontos) if t > agora]
            passados = len(pontos) - len(proximos)

            if passados:
                self.log(f"⚠️ {passados} horário(s) já passou/passarão - ignorado(s).")

            if not proximos:
                self.log("⚠️ Todos os horários já passaram hoje. Reinicie amanhã.")
                return

            self.log(f"📌 {len(proximos)} batida(s) agendada(s).")
            self.status("⏳ Aguardando próxima batida")

            for horario, nome, idx in proximos:
                if not _aguardar_ate_horario(
                    horario,
                    nome,
                    idx,
                    log=self.log,
                    pausa_evento=self.pausa_evento,
                    parar_evento=self.parar_evento,
                    status_callback=self.status,
                ):
                    self.log("🛑 Execução interrompida.")
                    self.status("🛑 Execução interrompida")
                    return

                if self.parar_evento.is_set():
                    self.log("🛑 Execução interrompida.")
                    self.status("🛑 Execução interrompida")
                    return

                executar_batida_com_navegador(
                    nome,
                    idx,
                    self.employee_id,
                    self.password,
                    log=self.log,
                )
                time.sleep(5)

            self.log("═" * 50)
            self.log("✅ TODAS AS BATIDAS DO DIA FORAM PROCESSADAS!")
            self.log("═" * 50)
            self.status("✅ Todas as batidas processadas")
        except RuntimeError as err:
            self.log(f"❌ {err}")
            self.status("❌ Falha no processamento")
        except Exception as err:
            self.log(f"❌ Erro inesperado: {err}")
            self.status("❌ Erro inesperado")
        finally:
            self.ativo = False
            self.pausa_evento.clear()
            if self.parar_evento.is_set():
                self.status("⚪ Pronto")


class PontoApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Ponto Automático")
        self.root.geometry("360x320")
        self.root.minsize(360, 300)
        self.root.resizable(True, True)
        self.root.configure(bg=UI_COLORS["bg"])

        if os.name == "nt":
            try:
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(APP_ID)
            except Exception:
                pass

        self.log_queue: Queue[str] = Queue()
        self.status_queue: Queue[str] = Queue()
        self.controller = PontoController(self._append_log, self._set_status)

        self.var_matricula = tk.StringVar()
        self.var_senha = tk.StringVar()
        self.var_salvar = tk.BooleanVar(value=False)
        self.var_mostrar_senha = tk.BooleanVar(value=False)

        self.tray_icon = None
        self.tray_thread: threading.Thread | None = None
        self.tray_suportado = False
        self.tray_verificado = False
        self.native_tray = NativeTrayManager(
            self.root,
            on_restore=self._mostrar,
            on_exit=self._encerrar_aplicacao,
            log=self._append_log,
            icon_path=LOGO_ICO,
        )
        self._logo_img = None

        self._aplicar_logo_janela()
        self._build_ui()
        self._carregar_credenciais_salvas()
        self._preparar_dependencias_bandeja()
        self.root.report_callback_exception = self._handle_tk_exception
        self.root.protocol("WM_DELETE_WINDOW", self._on_close_request)
        self.root.after(200, self._drain_logs)
        self.root.after(200, self._drain_status)
        self.root.after(500, self._sync_buttons)

        self._append_log("Aplicação pronta. Clique em Iniciar para agendar as batidas.")

    def _build_ui(self) -> None:
        card_config = tk.Frame(self.root, bg=UI_COLORS["card"], bd=0, highlightthickness=1)
        card_config.configure(highlightbackground=UI_COLORS["warning"], highlightcolor=UI_COLORS["warning"])
        card_config.pack(fill="x", padx=14, pady=(10, 10))

        lbl_config = tk.Label(
            card_config,
            text="Credenciais",
            font=("Segoe UI Semibold", 11),
            fg=UI_COLORS["text"],
            bg=UI_COLORS["card"],
        )
        lbl_config.grid(row=0, column=0, columnspan=4, sticky="w", padx=10, pady=(8, 4))

        tk.Label(
            card_config,
            text="Matrícula",
            fg=UI_COLORS["muted"],
            bg=UI_COLORS["card"],
            font=("Segoe UI", 9),
        ).grid(row=1, column=0, sticky="w", padx=(10, 6), pady=(0, 4))

        self.entry_matricula = tk.Entry(
            card_config,
            textvariable=self.var_matricula,
            bg=UI_COLORS["card_alt"],
            fg=UI_COLORS["text"],
            insertbackground=UI_COLORS["text"],
            relief="flat",
            width= 60,
            font=("Consolas", 10),
        )
        self.entry_matricula.grid(row=1, column=1, sticky="ew", padx=(0, 10), pady=(0, 4))

        tk.Label(
            card_config,
            text="Senha",
            fg=UI_COLORS["muted"],
            bg=UI_COLORS["card"],
            font=("Segoe UI", 9),
        ).grid(row=2, column=0, sticky="w", padx=(10, 6), pady=(0, 4))

        self.entry_senha = tk.Entry(
            card_config,
            textvariable=self.var_senha,
            show="*",
            bg=UI_COLORS["card_alt"],
            fg=UI_COLORS["text"],
            insertbackground=UI_COLORS["text"],
            relief="flat",
            width=20,
            font=("Consolas", 10),
        )
        self.entry_senha.grid(row=2, column=1, sticky="ew", padx=(0, 10), pady=(0, 4))

        chk_mostrar = tk.Checkbutton(
            card_config,
            text="Mostrar senha",
            variable=self.var_mostrar_senha,
            command=self._alternar_visibilidade_senha,
            bg=UI_COLORS["card"],
            fg=UI_COLORS["muted"],
            selectcolor=UI_COLORS["card"],
            activebackground=UI_COLORS["card"],
            activeforeground=UI_COLORS["text"],
            font=("Segoe UI", 9),
        )
        chk_mostrar.grid(row=2, column=2, sticky="w", padx=(0, 10), pady=(0, 4))

        chk_salvar = tk.Checkbutton(
            card_config,
            text="Salvar credenciais",
            variable=self.var_salvar,
            bg=UI_COLORS["card"],
            fg=UI_COLORS["muted"],
            selectcolor=UI_COLORS["card"],
            activebackground=UI_COLORS["card"],
            activeforeground=UI_COLORS["text"],
            font=("Segoe UI", 9),
        )
        chk_salvar.grid(row=3, column=0, columnspan=4, sticky="w", padx=10, pady=(0, 8))

        card_config.grid_columnconfigure(1, weight=1)

        frame_buttons = tk.Frame(self.root, bg=UI_COLORS["bg"])
        frame_buttons.pack(fill="x", padx=14, pady=(0, 8))

        self.btn_iniciar = tk.Button(frame_buttons, text="▶ Iniciar", width=7, command=self._iniciar)
        self._estilizar_botao(self.btn_iniciar, primary=True)
        self.btn_iniciar.pack(side="left", padx=(0, 8))

        self.btn_pausar = tk.Button(frame_buttons, text="⏸ Pausar", width=7, state="disabled", command=self._pausar)
        self._estilizar_botao(self.btn_pausar)
        self.btn_pausar.pack(side="left", padx=(0, 8))

        self.btn_esconder = tk.Button(frame_buttons, text="🠋 Esconder", width=8, command=self._esconder)
        self._estilizar_botao(self.btn_esconder)
        self.btn_esconder.pack(side="left")

        self.btn_sair = tk.Button(frame_buttons, text="✖ Sair", width=7, command=self._sair_com_confirmacao)
        self._estilizar_botao(self.btn_sair, danger=True)
        self.btn_sair.pack(side="left", padx=(8, 0))

        self.lbl_contagem = tk.Label(
            self.root,
            text="Status: aguardando início",
            fg=UI_COLORS["accent"],
            bg=UI_COLORS["bg"],
            font=("Segoe UI Semibold", 10),
            anchor="w",
        )
        self.lbl_contagem.pack(fill="x", padx=14, pady=(0, 6))

        self.txt_logs = tk.Text(
            self.root,
            wrap="word",
            height=9,
            bg=UI_COLORS["log_bg"],
            fg=UI_COLORS["text"],
            insertbackground=UI_COLORS["text"],
            relief="flat",
            highlightthickness=1,
            highlightbackground=UI_COLORS["warning"],
            padx=10,
            pady=8,
            font=("Consolas", 10),
        )
        self.txt_logs.pack(fill="both", expand=True, padx=14, pady=(0, 12))
        self.txt_logs.configure(state="disabled")

    def _aplicar_logo_janela(self) -> None:
        if LOGO_ICO.exists():
            try:
                self.root.iconbitmap(str(LOGO_ICO))
            except Exception:
                pass

        if LOGO_PNG.exists():
            try:
                self._logo_img = tk.PhotoImage(file=str(LOGO_PNG))
                self.root.iconphoto(True, self._logo_img)
            except Exception:
                self._logo_img = None

    def _estilizar_botao(self, botao: tk.Button, primary: bool = False, danger: bool = False) -> None:
        if primary:
            bg = UI_COLORS["accent"]
            hover = UI_COLORS["accent_hover"]
            fg = "#001313"
        elif danger:
            bg = UI_COLORS["danger"]
            hover = "#bf3a3a"
            fg = "#fff4f4"
        else:
            bg = UI_COLORS["warning"]
            hover = "#354867"
            fg = UI_COLORS["text"]

        botao.configure(
            bg=bg,
            fg=fg,
            activebackground=hover,
            activeforeground=fg,
            relief="flat",
            bd=0,
            cursor="hand2",
            font=("Segoe UI Semibold", 10),
            padx=8,
            pady=7,
            disabledforeground="#7c8aa5",
        )

    def _carregar_credenciais_salvas(self) -> None:
        config = carregar_config()
        self.var_salvar.set(bool(config["save_credentials"]))

        if bool(config["save_credentials"]):
            self.var_matricula.set(str(config["employee_id"]))
            self.var_senha.set(str(config["password"]))
            self._append_log("🔐 Credenciais salvas carregadas.")

    def _alternar_visibilidade_senha(self) -> None:
        self.entry_senha.configure(show="" if self.var_mostrar_senha.get() else "*")

    def _preparar_dependencias_bandeja(self) -> None:
        self.tray_suportado = carregar_dependencias_bandeja(log=self._append_log)
        self.tray_verificado = True

    def _append_log(self, message: str) -> None:
        ts = datetime.now().strftime("%H:%M:%S")
        self.log_queue.put(f"[{ts}] {message}")

    def _drain_logs(self) -> None:
        changed = False
        while True:
            try:
                message = self.log_queue.get_nowait()
            except Empty:
                break
            changed = True
            self.txt_logs.configure(state="normal")
            self.txt_logs.insert("end", message + "\n")
            self.txt_logs.configure(state="disabled")

        if changed:
            self.txt_logs.see("end")

        self.root.after(200, self._drain_logs)

    def _set_status(self, message: str) -> None:
        self.status_queue.put(message)

    def _drain_status(self) -> None:
        latest = None
        while True:
            try:
                latest = self.status_queue.get_nowait()
            except Empty:
                break

        if latest is not None:
            self.lbl_contagem.configure(text=f"Status: {latest}")

        self.root.after(200, self._drain_status)

    def _sync_buttons(self) -> None:
        if self.controller.ativo:
            self.btn_iniciar.configure(state="disabled")
            self.btn_pausar.configure(state="normal")
        else:
            self.btn_iniciar.configure(state="normal")
            self.btn_pausar.configure(state="disabled", text="⏸ Pausar")
            if self.lbl_contagem.cget("text") in {"Status: 🛑 Execução interrompida", "Status: ⏹️ Encerrando..."}:
                self.lbl_contagem.configure(text="Status: ⚪ Pronto")
        self.root.after(500, self._sync_buttons)

    def _iniciar(self) -> None:
        matricula = self.var_matricula.get().strip()
        senha = self.var_senha.get()

        if not matricula or not senha:
            self._append_log("⚠️ Preencha matrícula e senha para iniciar.")
            return

        try:
            salvar_config(matricula, senha, self.var_salvar.get())
            if self.var_salvar.get():
                self._append_log("💾 Credenciais salvas para próximas execuções.")
            else:
                self._append_log("🧼 Credenciais removidas do arquivo local.")
        except Exception as err:
            self._append_log(f"⚠️ Não foi possível salvar configurações: {err}")

        self.controller.iniciar(matricula, senha)

    def _pausar(self) -> None:
        pausado = self.controller.pausar_ou_retornar()
        self.btn_pausar.configure(text="▶ Retomar" if pausado else "⏸ Pausar")

    def _create_tray_icon(self):
        if pystray is None or Image is None or ImageDraw is None:
            return None

        image = Image.new("RGB", (64, 64), color=(20, 20, 20))
        draw = ImageDraw.Draw(image)
        draw.rectangle((8, 8, 56, 56), fill=(0, 120, 215))
        draw.rectangle((20, 20, 44, 44), fill=(255, 255, 255))

        def on_show(icon, item):
            self.root.after(0, self._mostrar)

        def on_toggle_pause(icon, item):
            self.root.after(0, self._pausar)

        def on_exit(icon, item):
            self.root.after(0, self._encerrar_aplicacao)

        menu = pystray.Menu(
            pystray.MenuItem("Mostrar", on_show),
            pystray.MenuItem("Pausar/Retomar", on_toggle_pause),
            pystray.MenuItem("Sair", on_exit),
        )
        return pystray.Icon("ponto_automatico", image, "Ponto Automático", menu)

    def _start_tray_if_needed(self) -> bool:
        if self.native_tray.available and self.native_tray.start():
            return True

        if self.tray_icon is not None:
            return True

        if not self.tray_verificado:
            self.tray_suportado = carregar_dependencias_bandeja(log=self._append_log)
            self.tray_verificado = True

        if not self.tray_suportado:
            return False

        icon = self._create_tray_icon()
        if icon is None:
            self._append_log("⚠️ Para esconder na bandeja, instale: pip install pystray pillow")
            return False

        self.tray_icon = icon

        def run_icon():
            try:
                self.tray_icon.run()
            except Exception as err:
                self._append_log(f"⚠️ Falha ao iniciar bandeja: {err}")

        self.tray_thread = threading.Thread(target=run_icon, daemon=True)
        self.tray_thread.start()
        return True

    def _esconder(self) -> None:
        try:
            ok = self._start_tray_if_needed()
            if ok:
                self.root.withdraw()
                self._append_log("🫥 Aplicação enviada para a bandeja de tarefas.")
            else:
                if self._minimizar_nativo_windows():
                    self._append_log("🫥 Aplicação minimizada para a barra de tarefas.")
                else:
                    self.root.iconify()
                    self._append_log("🫥 Aplicação minimizada (fallback Tkinter).")
        except Exception as err:
            self._append_log(f"❌ Falha ao esconder janela: {err}")
            try:
                self.root.iconify()
                self._append_log("🫥 Aplicação minimizada (recuperação de erro).")
            except Exception as err2:
                self._append_log(f"❌ Falha também no fallback de minimização: {err2}")

    def _minimizar_nativo_windows(self) -> bool:
        try:
            self.root.update_idletasks()
            hwnd = self.root.winfo_id()
            if os.name == "nt" and hwnd:
                user32 = ctypes.windll.user32
                sw_minimize = 6
                user32.ShowWindow(hwnd, sw_minimize)

                parent_hwnd = user32.GetParent(hwnd)
                if parent_hwnd:
                    user32.ShowWindow(parent_hwnd, sw_minimize)

                self.root.iconify()
                return self.root.state() == "iconic"
        except Exception:
            return False
        return False

    def _handle_tk_exception(self, exc_type, exc_value, exc_tb) -> None:
        detalhe = "".join(traceback.format_exception(exc_type, exc_value, exc_tb)).strip()
        self._append_log(f"❌ Erro de interface: {exc_value}")
        self._append_log(f"📋 Detalhe técnico: {detalhe.splitlines()[-1] if detalhe else exc_value}")

    def _mostrar(self) -> None:
        if self.native_tray.active:
            self.native_tray.stop()

        self.root.deiconify()
        self.root.lift()
        self.root.focus_force()
        self._append_log("👁️ Janela restaurada.")

    def _on_close_request(self) -> None:
        resposta = messagebox.askyesnocancel(
            "Fechar aplicação",
            "Sim: esconder na bandeja\nNão: encerrar totalmente\nCancelar: voltar",
        )

        if resposta is None:
            return

        if resposta:
            self._esconder()
            return

        self._encerrar_aplicacao()

    def _sair_com_confirmacao(self) -> None:
        confirmar = messagebox.askyesno("Encerrar", "Deseja encerrar a aplicação agora?")
        if confirmar:
            self._encerrar_aplicacao()

    def _encerrar_aplicacao(self) -> None:
        self.controller.encerrar()
        self.native_tray.stop()
        if self.tray_icon is not None:
            try:
                self.tray_icon.stop()
            except Exception:
                pass
        self.root.destroy()


def main() -> None:
    root = tk.Tk()
    PontoApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()


