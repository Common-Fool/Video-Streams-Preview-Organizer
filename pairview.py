#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Video Manager (pairview.py) — просмотр превью, выборочное удаление, создание превью, запуск в MPC.

  python pairview.py ПАПКА                       видео и превью лежат вместе (подпапки тоже)
  python pairview.py ПАПКА --previews ПАПКА2     превью в отдельной папке (подпапки те же)
  python pairview.py ПАПКА --clean videos        показать видео, у которых нет превью
  python pairview.py ПАПКА --clean previews --apply   убрать превью, у которых нет видео
  python pairview.py ПАПКА --purge               удалить насовсем всё из ПАПКА/_на_удаление
  python pairview.py ПАПКА --ignore-ext ts,m2ts  не считать видео файлы .ts и .m2ts (по умолчанию игнорируется .ts)

Пара — файлы с одинаковым именем без расширения в одной подпапке.
«Удалить» переносит пару в ПАПКА/_на_удаление (мгновенно и обратимо). Кнопка «На удаление» в шапке
показывает, сколько там лежит, и очищает папку насовсем.
Вкладка «Видео без превью» создаёт недостающие превью через ffmpeg (нужен ffmpeg в PATH или --ffmpeg).
Превью по умолчанию: сетка 10×9 кадров, ширина 2560, на каждом кадре только время (--cols --rows --width --header).
Кнопка «Пересоздать превью» на вкладке «Превью» заменяет старые превью новыми (старые уходят в _на_удаление).
Кнопка «Убрать превью без видео» переносит такие превью в _на_удаление, «Обновить» (F5) перечитывает папку.
Видеокарта NVIDIA: --gpu on декодирует видео на ней; auto и off (по умолчанию auto) — процессор: для превью он не медленнее.
Своё окно: нужен pywebview (pip install pywebview); без него галерея откроется в браузере. --browser — всегда в браузере.
Запуск с ярлыка без консоли: pythonw.exe pairview.py "D:\Видео" (журнал и настройки — в %APPDATA%\pairview).
Без папки в командной строке открывается папка прошлого запуска; другую выбирает кнопка с именем папки в шапке.
ffmpeg.exe и ffprobe.exe можно положить рядом с программой: они находятся без PATH.
Постоянные параметры можно записать в pairview.json рядом со скриптом: {"folder": "D:\\Видео", "player": "...mpc-hc64.exe"}.
Папка из pairview.json берётся, только если папки прошлого запуска нет или она недоступна.
Только стандартная библиотека, Python 3.8+.
"""
import argparse
import atexit
import errno
import json
import os
import queue
import re
import secrets
import socket
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

VIDEO = {'.mp4', '.mkv', '.avi', '.mov', '.wmv', '.flv', '.webm', '.m4v',
         '.mpg', '.mpeg', '.ts', '.m2ts', '.3gp', '.ogv', '.vob'}
IMAGE = {'.jpg': 'image/jpeg', '.jpeg': 'image/jpeg', '.png': 'image/png',
         '.webp': 'image/webp', '.gif': 'image/gif', '.bmp': 'image/bmp',
         '.avif': 'image/avif'}
IGNORE = {'.ts'}        # расширения видео, файлы с которыми игнорируются (параметр --ignore-ext)
SCAN = {'ignored': 0}   # сколько файлов пропущено при последнем сканировании
TRASH = '_на_удаление'
TOKEN = secrets.token_urlsafe(12)
ROOT_NAME = ''
PLAYER = {'path': ''}  # путь к MPC-HC/MPC-BE (--player или автопоиск)
VROOT = ''   # корень с видео
PROOT = ''   # корень с превью (тот же, если превью лежат вместе с видео)

GROUPS = {}  # id -> {'name', 'dir', 'key', 'v': [файл], 'p': [файл]}; файл = (путь, корень, размер, mtime)
IDS = {'next': 0}  # следующий свободный номер пары (номера не переиспользуются)
UNDO = []    # стек отмены: каждая запись — список [(id, группа, [(откуда, куда)])]; одно действие = одна запись
LOCK = threading.RLock()  # защищает GROUPS и UNDO
ROOTLOCK = threading.Lock()  # смена открытой папки и rescan() не идут одновременно


# ───────────────────────── поиск пар ─────────────────────────

def walk(root):
    stack = [root]
    while stack:
        d = stack.pop()
        try:
            with os.scandir(d) as it:
                for e in it:
                    if e.is_dir(follow_symlinks=False):
                        # пропускаем корзину, скрытые папки, @eaDir и #recycle
                        if e.name != TRASH and e.name[0] not in '.@#':
                            stack.append(e.path)
                    elif e.is_file():
                        yield d, e
        except OSError as err:
            print('Пропущена папка', d, '—', err)


def scan(vroot, proot):
    groups = {}
    skipped = set()  # (подпапка, имя) файлов с игнорируемым расширением: к ним относятся и их превью
    SCAN['ignored'] = 0

    def add(root, want_v, want_p):
        for d, e in walk(root):
            stem, ext = os.path.splitext(e.name)
            ext = ext.lower()
            rel = os.path.relpath(d, root)
            key = (os.path.normcase(rel), stem.lower())
            if want_v and ext in IGNORE:
                SCAN['ignored'] += 1
                skipped.add(key)
                continue
            if want_v and ext in VIDEO:
                kind = 'v'
            elif want_p and ext in IMAGE:
                kind = 'p'
                inner = os.path.splitext(stem)[1].lower()
                if inner in VIDEO or inner in IGNORE:  # «клип.mp4.jpg» → «клип»
                    stem = os.path.splitext(stem)[0]
                    key = (key[0], stem.lower())
            else:
                continue
            try:
                st = e.stat()
            except OSError:
                continue
            g = groups.setdefault(key, {'name': stem, 'key': key,
                                        'dir': '' if rel == '.' else rel.replace(os.sep, '/'),
                                        'v': [], 'p': []})
            g[kind].append((e.path, root, st.st_size, st.st_mtime))

    same = os.path.normcase(vroot) == os.path.normcase(proot)
    if same:
        add(vroot, True, True)
    else:
        add(vroot, True, False)
        add(proot, False, True)
    for k in skipped:  # превью игнорируемого файла не показываем и не трогаем: «нет видео» тут было бы ложным
        g = groups.get(k)
        if g is not None and not g['v']:
            del groups[k]
    for g in groups.values():
        g['v'].sort()
        g['p'].sort()
    return groups
# ───────────────────────── файловые операции ─────────────────────────

class Fail(Exception):
    """Ожидаемая ошибка с понятным текстом и кодом HTTP."""

    def __init__(self, msg, code=400):
        Exception.__init__(self, msg)
        self.code = code


class Gone(LookupError):
    """Пары уже нет на сервере — интерфейсу нужно обновить список."""


class MoveError(Exception):
    """Не удалось перенести файл; хранит путь, исходную ошибку и место назначения."""

    def __init__(self, path, cause, dst=''):
        Exception.__init__(self, str(cause))
        self.path, self.cause, self.dst = path, cause, dst


def move(src, dst):
    """Только переименование: мгновенно и без скрытого копирования гигабайт.

    shutil.move при неудаче переименования молча копирует файл и удаляет оригинал — для видео
    на гигабайты это зависание, а при занятом файле ещё и лишние копии. Поэтому здесь os.rename;
    «файл занят» (плеер, проводник, антивирус, сетевая папка) повторяем несколько раз с паузами.
    """
    for attempt in range(6):
        try:
            os.rename(src, dst)
            return
        except PermissionError:
            if attempt == 5:
                raise
            time.sleep(0.3)


def explain(e):
    """Понятное объяснение сбоя переноса — что случилось и что делать."""
    c = e.cause if isinstance(e, MoveError) else e
    name = os.path.basename(getattr(e, 'path', '') or '')
    winerr = getattr(c, 'winerror', None)
    if winerr == 206 or c.errno == errno.ENAMETOOLONG or (winerr == 3 and len(getattr(e, 'dst', '')) >= 250):
        return 'слишком длинный путь для Windows: ' + name + '. Сократите имена папок или включите длинные пути'
    if isinstance(c, PermissionError):
        return ('файл занят другой программой (плеер, проводник, антивирус) или защищён от записи: ' + name +
                '. Закройте её и нажмите Del ещё раз')
    if isinstance(c, FileNotFoundError):
        return 'файл не найден: ' + name + '. Его убрали или переименовали вне галереи — список обновлён'
    if c.errno == errno.EXDEV:
        return 'файл лежит на другом диске, мгновенный перенос невозможен: ' + name
    return 'ошибка файловой системы (%s): %s' % (getattr(c, 'strerror', None) or c, name)


def trash_dst(path, root):
    dst = os.path.join(root, TRASH, os.path.relpath(path, root))
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    base, ext = os.path.splitext(dst)
    n = 0
    while os.path.exists(dst):
        n += 1
        dst = '%s (%d)%s' % (base, n, ext)
    return dst


def to_trash(path, root):
    dst = trash_dst(path, root)
    move(path, dst)
    return dst


def delete_group(gid):
    with LOCK:
        g = GROUPS.get(gid)
    if g is None:
        raise Gone('пары уже нет — список обновлён')
    moved = []
    for path, root, *_ in g['v'] + g['p']:  # видео первым: его чаще держит плеер
        dst = ''
        try:
            dst = trash_dst(path, root)
            move(path, dst)
        except OSError as e:
            for src, back in reversed(moved):  # откат, чтобы пара не развалилась
                try:
                    move(back, src)
                except OSError:
                    pass
            raise MoveError(path, e, dst)
        moved.append((path, dst))
    tstat_add(len(moved), sum(f[2] for f in g['v'] + g['p']))
    with LOCK:
        GROUPS.pop(gid, None)
        UNDO.append([(gid, g, moved)])


def delete_batch(ids, orphans_only=False):
    """Перенести пары в _на_удаление одним действием: Ctrl+Z вернёт все сразу.

    orphans_only=True — только превью без видео (видео так удалить нельзя: сервер сам проверяет, что его нет).
    Если файл одной пары занят, эта пара остаётся на месте, остальные переносятся; причина — в failed.
    """
    def wanted(g):
        return bool(g['p'] and not g['v']) if orphans_only else bool(g['v'] or g['p'])

    with LOCK:
        todo = [(i, GROUPS[i]) for i in dict.fromkeys(ids)
                if isinstance(i, int) and i in GROUPS and wanted(GROUPS[i])]
    batch, failed = [], []
    for gid, g in todo:
        moved = []
        path = dst = ''
        try:
            for path, root, *_ in (g['p'] if orphans_only else g['v'] + g['p']):  # видео первым: его чаще держит плеер
                dst = trash_dst(path, root)
                move(path, dst)
                moved.append((path, dst))
        except OSError as e:
            for src, back in reversed(moved):
                try:
                    move(back, src)
                except OSError:
                    pass
            failed.append({'name': g['name'], 'error': explain(MoveError(path, e, dst))})
            continue
        tstat_add(len(moved), sum(f[2] for f in (g['p'] if orphans_only else g['v'] + g['p'])))
        with LOCK:
            GROUPS.pop(gid, None)
        batch.append((gid, g, moved))
    if batch:
        with LOCK:
            UNDO.append(batch)
    return {'removed': len(batch), 'failed': failed, 'trash': trash_stats()}


def delete_orphans(ids):
    return delete_batch(ids, True)


def undo_last():
    """Вернуть последнее действие целиком (одну пару или всю пачку)."""
    with LOCK:
        if not UNDO:
            raise LookupError('нечего отменять')
        batch = UNDO[-1]
    if any(len(rec) > 3 for rec in batch):  # обрезка: пока пересоздаётся превью, файлы пары трогать нельзя
        with JLOCK:
            if JOB['running']:
                raise Fail('дождитесь, пока закончится создание превью', 409)
    first = None
    for rec in batch:
        gid, g, moved = rec[:3]
        for path, root in (rec[3] if len(rec) > 3 else ()):  # на месте оригинала лежит обрезанный файл: его — в корзину
            if os.path.exists(path):
                try:
                    size = os.path.getsize(path)
                    to_trash(path, root)
                    tstat_add(1, size)
                except OSError as e:
                    raise MoveError(path, e)
        for src, dst in moved:
            if os.path.exists(dst):
                try:
                    size = os.path.getsize(dst) if g is not None else 0
                    move(dst, src)
                    if g is None:
                        refresh_trash_stats()  # папка переехала целиком: размер посчитает фоновый обход
                    else:
                        tstat_add(-1, -size)
                except OSError as e:
                    raise MoveError(src, e, dst)
        if g is None:  # запись о переносе папки целиком: сами файлы уже вернулись переименованием папки
            continue
        with LOCK:
            for other in [i for i, x in GROUPS.items() if i != gid and x.get('key') == g.get('key')]:
                del GROUPS[other]  # такую же пару мог успеть создать «Обновить»
            GROUPS[gid] = g
        if first is None:
            first = gid
    with LOCK:
        if UNDO and UNDO[-1] is batch:
            UNDO.pop()
    return first


def new_id():
    """Свободный номер пары: не совпадает ни с парами в списке, ни с удалёнными (они вернутся по Ctrl+Z)."""
    with LOCK:
        used = set(GROUPS)
        for batch in UNDO:
            used.update(x[0] for x in batch)
        IDS['next'] = max(IDS['next'], max(used, default=-1) + 1)
        IDS['next'] += 1
        return IDS['next'] - 1


def rescan():
    """Перечитать папки: подхватить новые файлы и убрать пропавшие. Номера прежних пар сохраняются."""
    with ROOTLOCK:  # смена папки посреди обхода смешала бы старую папку с новой
        return _rescan()


def _rescan():
    fresh = scan(VROOT, PROOT)
    ignored = SCAN['ignored']
    with LOCK:
        def files(gs):
            return {f[0]: kind for g in gs for kind in ('v', 'p') for f in g[kind]}
        before = files(GROUPS.values())
        by_key = {g.get('key'): gid for gid, g in GROUPS.items()}
        with JLOCK:
            busy = set(JOB['active'])  # этими парами сейчас занят ffmpeg — их превью допишет сам процесс
        for key, ng in fresh.items():
            gid = by_key.get(key)
            if gid is None:
                GROUPS[new_id()] = ng
                continue
            g = GROUPS[gid]
            g['name'], g['dir'] = ng['name'], ng['dir']
            if gid in busy:
                continue
            g['v'][:] = ng['v']
            g['p'][:] = ng['p']
        for key, gid in by_key.items():
            if key not in fresh and gid not in busy:
                del GROUPS[gid]
        after = files(GROUPS.values())
    SCAN['ignored'] = ignored
    new = [p for p in after if p not in before]
    return {'added_videos': sum(1 for p in new if after[p] == 'v'),
            'added_previews': sum(1 for p in new if after[p] == 'p'),
            'gone': sum(1 for p in before if p not in after)}


# ───────────────────────── запуск программ и вывод окна на передний план ─────────────────────────

# окна проигрывателей, которые подходят, даже если в заголовке нет имени файла (MPC-HC, MPC-BE, PotPlayer)
PLAYER_CLASSES = ('mediaplayerclassicw', 'mpc-be', 'potplayer', 'potplayer64')


def pick_window(windows, path, player_only=False):
    """Выбрать окно плеера или проводника: в заголовке стоит имя файла или папки.

    windows — список (hwnd, заголовок) или (hwnd, заголовок, класс окна). Окно браузера с галереей не подходит:
    в его заголовке имени файла нет. Если заголовок имени не содержит (в MPC можно отключить показ имени),
    для видео берётся окно MPC или PotPlayer по классу окна.
    """
    name = path.rstrip('\\/').replace('\\', '/').split('/')[-1].lower()
    stem = os.path.splitext(name)[0] if '.' in name else name
    items = [(w[0], (w[1] or '').lower(), (w[2] if len(w) > 2 else '').lower()) for w in windows]
    if player_only:  # после «в плейлист MPC» файла в заголовке может не быть — берём окно плеера по классу
        return next((hwnd for hwnd, _t, cls in items if cls in PLAYER_CLASSES), None)
    for hwnd, title, _cls in items:
        if title and name in title:
            return hwnd
    if len(stem) >= 4:
        for hwnd, title, _cls in items:
            if title and stem in title:
                return hwnd
    if os.path.splitext(name)[1].lower() in VIDEO:
        for hwnd, _title, cls in items:
            if cls in PLAYER_CLASSES:
                return hwnd
    return None


def _user32():
    """user32 с описанными типами аргументов: дескрипторы окон на 64-битной Windows нельзя передавать как обычные int."""
    import ctypes
    from ctypes import wintypes
    u = ctypes.WinDLL('user32')
    u.IsWindowVisible.argtypes = [wintypes.HWND]
    u.GetWindowTextLengthW.argtypes = [wintypes.HWND]
    u.GetWindowTextW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    u.GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    u.IsIconic.argtypes = [wintypes.HWND]
    u.ShowWindow.argtypes = [wintypes.HWND, ctypes.c_int]
    u.GetForegroundWindow.restype = wintypes.HWND
    u.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    u.GetWindowThreadProcessId.restype = wintypes.DWORD
    u.AttachThreadInput.argtypes = [wintypes.DWORD, wintypes.DWORD, wintypes.BOOL]
    u.BringWindowToTop.argtypes = [wintypes.HWND]
    u.SetForegroundWindow.argtypes = [wintypes.HWND]
    u.SwitchToThisWindow.argtypes = [wintypes.HWND, wintypes.BOOL]
    u.SetWindowPos.argtypes = [wintypes.HWND, wintypes.HWND, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wintypes.UINT]
    return u


def list_windows():
    """Видимые окна верхнего уровня: (hwnd, заголовок, класс окна). Только Windows."""
    import ctypes
    from ctypes import wintypes
    user32 = _user32()
    out = []

    @ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
    def cb(hwnd, _lp):
        if user32.IsWindowVisible(hwnd):
            n = user32.GetWindowTextLengthW(hwnd)
            if n:
                buf = ctypes.create_unicode_buffer(n + 1)
                user32.GetWindowTextW(hwnd, buf, n + 1)
                cls = ctypes.create_unicode_buffer(256)
                user32.GetClassNameW(hwnd, cls, 256)
                out.append((hwnd, buf.value, cls.value))
        return True

    user32.EnumWindows(cb, 0)
    return out


def raise_window(hwnd):
    """Вывести окно на передний план БЕЗ эмуляции нажатий клавиш.

    Раньше для этого «нажимался» Alt, а одиночный Alt включает в MPC режим меню: плеер вёл себя странно, пока не нажмёшь Esc.
    Теперь по очереди: подключиться к потоку активного окна и вызвать SetForegroundWindow → SwitchToThisWindow
    (то же, что делает Alt+Tab) → поднять окно поверх остальных (оно будет видно, даже если Windows не отдала фокус).
    """
    import ctypes
    from ctypes import wintypes
    user32 = _user32()
    kernel32 = ctypes.WinDLL('kernel32')
    kernel32.GetCurrentThreadId.restype = wintypes.DWORD
    if user32.IsIconic(hwnd):
        user32.ShowWindow(hwnd, 9)  # SW_RESTORE
    fg = user32.GetForegroundWindow()
    fg_thread = user32.GetWindowThreadProcessId(fg, None) if fg else 0
    me = kernel32.GetCurrentThreadId()
    attached = bool(fg_thread and fg_thread != me and user32.AttachThreadInput(me, fg_thread, True))
    try:
        user32.BringWindowToTop(hwnd)
        user32.ShowWindow(hwnd, 5)  # SW_SHOW
        user32.SetForegroundWindow(hwnd)
    finally:
        if attached:
            user32.AttachThreadInput(me, fg_thread, False)
    if user32.GetForegroundWindow() != hwnd:
        user32.SwitchToThisWindow(hwnd, True)
    if user32.GetForegroundWindow() != hwnd:
        # фокус не отдали — хотя бы показать окно поверх остальных (флаги: не двигать, не менять размер, показать)
        user32.SetWindowPos(hwnd, -1, 0, 0, 0, 0, 0x0043)  # HWND_TOPMOST
        user32.SetWindowPos(hwnd, -2, 0, 0, 0, 0, 0x0043)  # HWND_NOTOPMOST: вернуть обычный порядок окон
    return user32.GetForegroundWindow() == hwnd


def bring_to_front(path, wait=8.0, lister=None, raiser=None, sleep=time.sleep, player_only=False):
    """Подождать, пока откроется окно с этим файлом или папкой, и вывести его вперёд (повторяя, пока не выйдет)."""
    lister = lister or list_windows
    raiser = raiser or raise_window
    deadline = time.time() + wait
    done = 0
    while time.time() < deadline:
        try:
            hwnd = pick_window(lister(), path, player_only)
            if hwnd:
                if raiser(hwnd):
                    return True
                done += 1
                if done >= 4:  # окно нашли и четыре раза пытались — достаточно
                    return False
        except Exception:  # noqa: BLE001 — это удобство, а не основная работа: любой сбой молча пропускаем
            return False
        sleep(0.25)
    return False


def open_file(path, front=False):
    """Открыть файл или папку программой по умолчанию; front — вывести её окно на передний план (Windows)."""
    if sys.platform.startswith('win'):
        os.startfile(path)
        if front:
            threading.Thread(target=bring_to_front, args=(path,), daemon=True).start()
    elif sys.platform == 'darwin':
        subprocess.Popen(['open', path])
    else:
        subprocess.Popen(['xdg-open', path])


# ───────────────────────── папка «на удаление» ─────────────────────────

def trash_dirs():
    roots = [VROOT] if PROOT == VROOT else [VROOT, PROOT]
    return [os.path.join(r, TRASH) for r in roots]


TSTAT = {'files': 0, 'bytes': 0, 'ready': False, 'gen': 0}  # счётчик папки «на удаление»: хранится в памяти
TLOCK = threading.Lock()


def trash_walk():
    files = size = 0
    for d in trash_dirs():
        for dp, _dn, fn in os.walk(d):
            for f in fn:
                try:
                    size += os.path.getsize(os.path.join(dp, f))
                    files += 1
                except OSError:
                    pass
    return files, size


def refresh_trash_stats(wait=False):
    """Пересчитать счётчик «на удаление» обходом папки.

    По сети (NAS) обход тысяч файлов занимает десятки секунд, а раньше он выполнялся при КАЖДОМ удалении и каждой
    загрузке списка. Теперь обход идёт в фоне (wait=False), а между пересчётами счётчик обновляется на ходу.
    Пока идёт пересчёт, в ответах стоит pending=True.
    """
    def work():
        files, size = trash_walk()
        with TLOCK:
            if TSTAT['gen'] == gen:  # иначе за это время начат новый пересчёт (например, открыта другая папка)
                TSTAT.update(files=files, bytes=size, ready=True)

    with TLOCK:
        TSTAT['ready'] = False
        TSTAT['gen'] += 1
        gen = TSTAT['gen']
    if wait:
        work()
    else:
        threading.Thread(target=work, daemon=True).start()


def tstat_add(files, size):
    with TLOCK:
        TSTAT['files'] = max(0, TSTAT['files'] + files)
        TSTAT['bytes'] = max(0, TSTAT['bytes'] + size)


def trash_stats():
    with TLOCK:
        return {'files': TSTAT['files'], 'bytes': TSTAT['bytes'], 'pending': not TSTAT['ready']}


def remove_file(path):
    """Удалить файл; только для чтения — снять атрибут; занятый — повторить с паузами."""
    for attempt in range(4):
        try:
            os.remove(path)
            return
        except PermissionError:
            try:
                os.chmod(path, stat.S_IWRITE | stat.S_IREAD)
            except OSError:
                pass
            if attempt == 3:
                raise
            time.sleep(0.3)


def purge():
    """Удалить насовсем всё, что лежит в папках «на удаление». Ничего за их пределами не трогает."""
    removed = freed = 0
    failed = []
    for d in trash_dirs():
        # удаляем только папку с точным именем TRASH прямо внутри корня — и не ходим по ссылкам
        if os.path.basename(d) != TRASH or os.path.islink(d) or not os.path.isdir(d):
            continue
        for dp, dn, fn in os.walk(d, topdown=False, followlinks=False):
            for f in fn:
                p = os.path.join(dp, f)
                try:
                    size = os.path.getsize(p) if not os.path.islink(p) else 0
                    remove_file(p)
                    removed += 1
                    freed += size
                except OSError as e:
                    failed.append({'path': p, 'error': getattr(e, 'strerror', None) or str(e)})
            for sub in dn:
                sp = os.path.join(dp, sub)
                try:
                    os.unlink(sp) if os.path.islink(sp) else os.rmdir(sp)
                except OSError:
                    pass
        try:
            os.rmdir(d)
        except OSError:
            pass
    with LOCK:
        UNDO.clear()  # возвращать больше нечего
    refresh_trash_stats(wait=True)  # после очистки в корзине почти ничего нет: обход быстрый
    return {'removed': removed, 'bytes': freed, 'failed': failed, 'trash': trash_stats()}


def open_trash():
    for d in trash_dirs():
        if os.path.isdir(d):
            open_file(d, front=True)
            return
    raise Fail('папка %s пуста или ещё не создана' % TRASH)


def listing():
    with LOCK:
        snap = sorted(GROUPS.items(), key=lambda kv: kv[0])
        undo = len(UNDO)
    items, videos = [], []
    for gid, g in snap:
        vs, ps = g['v'], g['p']
        if ps:
            items.append({'id': gid, 'name': g['name'], 'dir': g['dir'], 'nv': len(vs),
                          'size': sum(f[2] for f in vs),
                          'mtime': max(f[3] for f in (vs or ps)), 'pm': max(f[3] for f in ps)})
        elif vs:
            videos.append({'id': gid, 'name': g['name'], 'file': os.path.basename(vs[0][0]),
                           'dir': g['dir'], 'size': sum(f[2] for f in vs), 'mtime': vs[0][3]})
    return {'items': items, 'videos': videos, 'undo': undo, 'root': ROOT_NAME, 'rootPath': VROOT, 'recent': recent_roots(),
            'cut': cut_status(),
            'trash': trash_stats(), 'ff': ff_info(), 'job': job_status(),
            'ign': {'exts': sorted(IGNORE), 'files': SCAN['ignored']}, 'mpc': player_info(),
            'opts': {'cols': OPTS['cols'], 'rows': OPTS['rows'], 'width': OPTS['width'], 'header': OPTS['header'],
                     'hw': gpu_info()}}


# ───────────────────────── настройки, плеер MPC, проводник ─────────────────────────

SLOCK = threading.Lock()
HAS_CONSOLE = [True]  # False при запуске через pythonw: тогда вывод идёт в журнал, а ошибки — в окно сообщения

# путь к MPC-HC из K-Lite указан первым: он есть у пользователя. Остальные — стандартные места установки.
MPC_DEFAULT = r'C:\Program Files (x86)\K-Lite Codec Pack\MPC-HC64\mpc-hc64.exe'
MPC_SUBDIRS = (r'K-Lite Codec Pack\MPC-HC64\mpc-hc64.exe', r'K-Lite Codec Pack\MPC-HC\mpc-hc.exe',
               r'MPC-HC\mpc-hc64.exe', r'MPC-HC\mpc-hc.exe', r'MPC-HC x64\mpc-hc64.exe',
               r'MPC-BE\mpc-be64.exe', r'MPC-BE\mpc-be.exe', r'MPC-BE x64\mpc-be64.exe')


def base_dir():
    """Папка, где лежит сама программа: рядом с pairview.exe (собранная версия) или с pairview.py.

    В собранном onefile-exe __file__ указывает во временную папку распаковки, поэтому берём путь к самому exe.
    """
    if getattr(sys, 'frozen', False):
        return os.path.dirname(os.path.abspath(sys.executable))
    return os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() else os.getcwd()


def app_dir():
    """Папка настроек и журнала: %APPDATA%\\pairview, ~/.config/pairview или то, что задано в PAIRVIEW_HOME."""
    base = os.environ.get('PAIRVIEW_HOME')
    if not base:
        if os.name == 'nt':
            base = os.path.join(os.environ.get('APPDATA') or os.path.expanduser('~'), 'pairview')
        else:
            base = os.path.join(os.environ.get('XDG_CONFIG_HOME') or os.path.expanduser('~/.config'), 'pairview')
    return base


def settings_file():
    return os.path.join(app_dir(), 'settings.json')


def read_all_settings():
    try:
        with open(settings_file(), encoding='utf-8') as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def write_all_settings(d):
    os.makedirs(app_dir(), exist_ok=True)
    tmp = settings_file() + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as f:
        json.dump(d, f, ensure_ascii=False, indent=1)
    os.replace(tmp, settings_file())


def root_key():
    return os.path.normcase(os.path.abspath(VROOT))


def load_settings():
    """Настройки интерфейса для этой папки (порядок, размер плиток, исключённые папки…)."""
    d = (read_all_settings().get('roots') or {}).get(root_key()) or {}
    return {k: v for k, v in d.items() if isinstance(k, str) and isinstance(v, str)}


def save_settings(new):
    clean = {k: v for k, v in new.items()
             if isinstance(k, str) and isinstance(v, str) and len(k) < 64 and len(v) < 200000}
    with SLOCK:
        d = read_all_settings()
        d.setdefault('roots', {})[root_key()] = clean
        try:
            write_all_settings(d)
        except OSError as e:
            print('Не удалось сохранить настройки:', e)


RECENT_MAX = 10


def recent_list(d):
    """Недавние папки из настроек: [{'folder', 'previews'}], первая — последняя открытая."""
    out = []
    for r in d.get('recent') or []:
        if isinstance(r, dict) and isinstance(r.get('folder'), str) and r['folder']:
            p = r.get('previews')
            out.append({'folder': r['folder'], 'previews': p if isinstance(p, str) else ''})
    return out


def remember_folder(path, previews=''):
    """Запомнить открытую папку: с неё начнётся следующий запуск, и она встанет первой в список недавних."""
    previews = '' if not previews or previews == path else previews
    with SLOCK:
        d = read_all_settings()
        d['last_folder'] = path
        d['last_previews'] = previews
        rest = [r for r in recent_list(d) if os.path.normcase(r['folder']) != os.path.normcase(path)]
        d['recent'] = ([{'folder': path, 'previews': previews}] + rest)[:RECENT_MAX]
        try:
            write_all_settings(d)
        except OSError:
            pass


def last_root():
    """Папка прошлого запуска и её отдельная папка превью: ('', '') — если не запоминалась или сейчас недоступна."""
    d = read_all_settings()
    v, p = d.get('last_folder'), d.get('last_previews')
    p = p if isinstance(p, str) else ''
    if not isinstance(v, str) or not v:
        return '', ''
    if not os.path.isdir(v) or (p and not os.path.isdir(p)):
        print('Папка прошлого запуска недоступна: %s' % (v if not os.path.isdir(v) else p))
        return '', ''
    return v, p


def recent_roots():
    """Недавние папки для страницы, кроме открытой. Доступность не проверяется: NAS может отвечать долго."""
    cur = os.path.normcase(VROOT)
    return [{'folder': r['folder'], 'name': os.path.basename(r['folder'].rstrip('\\/')) or r['folder']}
            for r in recent_list(read_all_settings()) if os.path.normcase(r['folder']) != cur]


def recent_previews(folder):
    """Отдельная папка превью, с которой эта папка открывалась раньше; None — папки нет в списке недавних."""
    for r in recent_list(read_all_settings()):
        if os.path.normcase(r['folder']) == os.path.normcase(folder):
            return r['previews']
    return None


def natural(s):
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r'(\d+)', s)]


def find_player(hint=None):
    """Найти MPC-HC или MPC-BE: сначала путь из параметра, потом K-Lite, потом стандартные папки и PATH."""
    cands = []
    if hint:
        if os.path.isdir(hint):
            cands += [os.path.join(hint, n) for n in ('mpc-hc64.exe', 'mpc-hc.exe', 'mpc-be64.exe', 'mpc-be.exe')]
        cands.append(hint)
    cands.append(MPC_DEFAULT)
    bases = [os.environ.get(k) for k in ('ProgramFiles', 'ProgramFiles(x86)', 'ProgramW6432')]
    bases += [r'C:\Program Files', r'C:\Program Files (x86)']
    for b in dict.fromkeys(x for x in bases if x):
        cands += [os.path.join(b, s) for s in MPC_SUBDIRS]
    cands += [shutil.which(n) for n in ('mpc-hc64', 'mpc-hc', 'mpc-be64', 'mpc-be')]
    return next((c for c in cands if c and os.path.isfile(c)), '')


def player_info():
    p = PLAYER['path']
    return {'ok': bool(p), 'name': ('MPC-BE' if 'mpc-be' in os.path.basename(p).lower() else 'MPC-HC') if p else ''}


def tree_key(g):
    """Порядок как в галерее: файлы корня, затем папки по дереву; внутри папки имена по-человечески (2 раньше 10)."""
    return ([natural(x) for x in g['dir'].split('/')] if g['dir'] else [], natural(g['name']))


def folder_videos(rel, deep):
    """Видеофайлы папки (и подпапок, если deep) в том порядке, в каком они идут в дереве. Игнорируемые не входят."""
    def inside(d):
        return d == rel or (deep and (rel == '' or d.startswith(rel + '/')))

    with LOCK:
        groups = [g for g in GROUPS.values() if g['v'] and inside(g['dir'])]
    groups.sort(key=tree_key)
    return [f[0] for g in groups for f in g['v']]


def mpc_files(ids):
    """Видео выбранных пар в порядке галереи."""
    with LOCK:
        groups = [GROUPS[i] for i in dict.fromkeys(ids) if isinstance(i, int) and i in GROUPS and GROUPS[i]['v']]
    groups.sort(key=tree_key)
    return [f[0] for g in groups for f in g['v']]


def send_to_mpc(files, add):
    """Передать видео в MPC.

    add=False — как «Play with MPC-HC» в проводнике: плейлист заменяется и воспроизведение начинается сразу.
    add=True — как «Add to MPC-HC playlist»: видео дописываются в конец плейлиста, воспроизведение не запускается
    (ключ /add только добавляет). Файлы передаются списком, а не папкой: так не попадают игнорируемые .ts, а порядок
    совпадает с галереей. Командная строка Windows ограничена 32 767 знаками, поэтому длинный список идёт
    несколькими вызовами: первый (при воспроизведении) без /add, остальные с /add.
    """
    if not PLAYER['path']:
        raise Fail('MPC не найден. Укажите путь параметром --player "C:\\...\\mpc-hc64.exe" или в файле pairview.json')
    files = [f for f in files if os.path.isfile(f)]
    if not files:
        raise Fail('в этой папке нет видео')
    chunks, cur, size = [], [], 0
    for f in files:
        n = len(f) + 3
        if cur and size + n > 24000:
            chunks.append(cur)
            cur, size = [], 0
        cur.append(f)
        size += n
    chunks.append(cur)
    for i, ch in enumerate(chunks):
        try:
            subprocess.Popen([PLAYER['path']] + (['/add'] if (add or i > 0) else []) + ch)
        except OSError as e:
            raise Fail('не удалось запустить %s: %s' % (PLAYER['path'], getattr(e, 'strerror', None) or e), 500)
        if i + 1 < len(chunks):
            time.sleep(1.5)  # дать первому экземпляру подняться, иначе следующий вызов откроет второе окно
    if os.name == 'nt':
        threading.Thread(target=bring_to_front, args=('',), kwargs={'player_only': True}, daemon=True).start()
    return {'added': len(files), 'calls': len(chunks)}


def inside_root(rel):
    """Папка ВНУТРИ выбранной корневой: относительный путь от клиента проверяется, выйти за корень нельзя."""
    parts = [x for x in (rel or '').replace('\\', '/').split('/') if x not in ('', '.')]
    if '..' in parts:
        raise Fail('недопустимая папка')
    path = os.path.normpath(os.path.join(VROOT, *parts))
    if os.path.commonpath([os.path.normcase(VROOT), os.path.normcase(path)]) != os.path.normcase(VROOT):
        raise Fail('недопустимая папка')
    return path


def show_in_explorer(rel=None, gid=None):
    """Открыть папку в проводнике; если задан номер пары — открыть её папку с выделенным файлом."""
    if gid is not None:
        with LOCK:
            g = GROUPS.get(gid)
        if g is None:
            raise Gone('пары уже нет — список обновлён')
        target, select = (g['v'] or g['p'])[0][0], True
    else:
        target, select = inside_root(rel), False
        if not os.path.isdir(target):
            raise Fail('папки нет на диске: ' + target)
    hint = os.path.dirname(target) if select else target
    if os.name == 'nt':
        if select:
            subprocess.Popen(['explorer.exe', '/select,', target])  # explorer всегда отвечает кодом 1 — это нормально
        else:
            os.startfile(target)
        threading.Thread(target=bring_to_front, args=(hint,), daemon=True).start()
    else:
        open_file(hint)
    return {'ok': True}


# ───────────────────────── удаление папок: пустых и целиком ─────────────────────────

JUNK_FILES = {'thumbs.db', 'desktop.ini', '.ds_store'}  # такие файлы пустую папку «непустой» не делают


def norm_rel(rel):
    return '/'.join(x for x in (rel or '').replace('\\', '/').split('/') if x not in ('', '.'))


def _scan_empty(d, out):
    """True — в папке d (или глубже) есть настоящие файлы. Пустые подпапки верхнего уровня кладутся в out.

    Корзина, системные папки (@eaDir, #recycle, .что-то) и Thumbs.db/desktop.ini содержимым не считаются.
    Символические ссылки считаются файлами: по ним ничего не удаляется.
    Если папку прочитать не вышло, она считается непустой: лучше пропустить, чем удалить лишнее.
    """
    try:
        with os.scandir(d) as it:
            entries = list(it)
    except OSError:
        return True
    found, mine = False, []
    for e in entries:
        try:
            is_dir = e.is_dir(follow_symlinks=False)
        except OSError:
            found = True
            continue
        if is_dir:
            if e.name == TRASH or e.name[0] in '.@#':
                continue
            inner = []
            if _scan_empty(e.path, inner):
                found = True
                mine.extend(inner)
            else:
                mine.append(e.path)  # папка целиком пуста: она сама кандидат, вложенные отдельно не перечисляем
        elif e.name.lower() not in JUNK_FILES:
            found = True
    if found:
        out.extend(mine)
    return found


def is_empty_dir(path):
    return os.path.isdir(path) and not _scan_empty(path, [])


def find_empty_dirs():
    """Пустые папки (верхнего уровня: вложенные в пустую уедут вместе с ней). Корневая папка в список не входит."""
    found = []
    _scan_empty(VROOT, found)
    rels = []
    for path in found:
        rel = os.path.relpath(path, VROOT).replace(os.sep, '/')
        if PROOT != VROOT:  # отдельная папка превью: парная папка там тоже должна быть пустой или отсутствовать
            other = os.path.join(PROOT, *rel.split('/'))
            if os.path.isdir(other) and not is_empty_dir(other):
                continue
        rels.append(rel)
    return sorted(rels, key=lambda r: [natural(x) for x in r.split('/')])


def trash_dir_dst(path, root):
    dst = os.path.join(root, TRASH, os.path.relpath(path, root))
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    base, n = dst, 0
    while os.path.exists(dst):
        n += 1
        dst = '%s (%d)' % (base, n)
    return dst


def trash_folder(rel):
    """Перенести папку целиком (с подпапками и любыми файлами) в _на_удаление одним переименованием.

    С отдельной папкой превью переносится и парная папка там. Возвращает список (откуда, куда).
    """
    parts = norm_rel(rel).split('/')
    pairs = []
    path = dst = ''
    try:
        for root in ([VROOT] if PROOT == VROOT else [VROOT, PROOT]):
            path = os.path.normpath(os.path.join(root, *parts))
            if not os.path.isdir(path):
                continue
            dst = trash_dir_dst(path, root)
            move(path, dst)
            pairs.append((path, dst))
    except OSError as e:
        for src, back in reversed(pairs):
            try:
                move(back, src)
            except OSError:
                pass
        raise MoveError(path, e, dst)
    return pairs


def folder_info(rel):
    """Что лежит в папке — для окна подтверждения перед удалением."""
    rel = norm_rel(rel)
    if not rel:
        raise Fail('корневую папку удалить нельзя: выберите подпапку')
    inside_root(rel)
    parts = rel.split('/')
    files = size = dirs = 0
    found = False
    for root in ([VROOT] if PROOT == VROOT else [VROOT, PROOT]):
        base = os.path.join(root, *parts)
        if not os.path.isdir(base):
            continue
        found = True
        for dp, dn, fn in os.walk(base):
            dn[:] = [d for d in dn if d != TRASH and d[0] not in '.@#']  # системные папки в счёт не идут
            dirs += len(dn)
            for f in fn:
                if f.lower() in JUNK_FILES:
                    continue
                try:
                    size += os.path.getsize(os.path.join(dp, f))
                    files += 1
                except OSError:
                    pass
    if not found:
        raise Fail('папки нет на диске: ' + rel)
    with LOCK:
        groups = [g for g in GROUPS.values() if g['dir'] == rel or g['dir'].startswith(rel + '/')]
    media = sum(len(g['v']) + len(g['p']) for g in groups)
    return {'dirs': dirs, 'files': files, 'bytes': size,
            'pairs': sum(1 for g in groups if g['v'] and g['p']),
            'videos_only': sum(1 for g in groups if g['v'] and not g['p']),
            'previews_only': sum(1 for g in groups if g['p'] and not g['v']),
            'other': max(0, files - media)}


def delete_folder(rel):
    """Перенести выбранную папку со всем содержимым в _на_удаление. Ctrl+Z вернёт папку и пары в список."""
    rel = norm_rel(rel)
    if not rel:
        raise Fail('корневую папку удалить нельзя: выберите подпапку')
    inside_root(rel)
    with JLOCK:
        running = JOB['running']
    if running:
        raise Fail('идёт создание превью: остановите его или дождитесь конца, потом удаляйте папки', 409)
    pairs = trash_folder(rel)
    if not pairs:
        raise Fail('папки нет на диске: ' + rel)
    with LOCK:
        gone = [(gid, g) for gid, g in GROUPS.items() if g['dir'] == rel or g['dir'].startswith(rel + '/')]
        for gid, _g in gone:
            del GROUPS[gid]
        UNDO.append([(None, None, pairs)] + [(gid, g, []) for gid, g in gone])
    refresh_trash_stats()
    return {'removed': len(gone), 'trash': trash_stats()}


def delete_empty(dirs):
    """Перенести пустые папки в _на_удаление. Перед переносом каждая проверяется ещё раз."""
    pairs, failed, done = [], [], 0
    for rel in dict.fromkeys(norm_rel(x) for x in dirs if isinstance(x, str)):
        if not rel:
            continue
        try:
            path = inside_root(rel)
        except Fail:
            continue
        if not is_empty_dir(path):  # между поиском и подтверждением в папку могли что-то положить
            continue
        if PROOT != VROOT:
            other = os.path.join(PROOT, *rel.split('/'))
            if os.path.isdir(other) and not is_empty_dir(other):
                continue
        try:
            pairs += trash_folder(rel)
            done += 1
        except MoveError as e:
            failed.append({'name': rel, 'error': explain(e)})
    if pairs:
        with LOCK:
            UNDO.append([(None, None, pairs)])
    if pairs:
        refresh_trash_stats()
    return {'removed': done, 'failed': failed, 'trash': trash_stats()}


# ───────────────────────── создание превью (ffmpeg) ─────────────────────────

class Cancelled(Exception):
    pass


FF = {'ok': False, 'ffmpeg': '', 'ffprobe': '', 'version': '', 'drawtext': False, 'font': ''}
OPTS = {'cols': 10, 'rows': 9, 'width': 2560, 'jobs': max(2, min(6, (os.cpu_count() or 4) // 2)), 'header': False}
JOB = {'running': False, 'stopped': False, 'redo': False, 'total': 0, 'done': 0, 'ok': 0,
       'failed': {}, 'active': {}, 'started': 0.0}
GPU = {'mode': 'auto', 'avail': False, 'by': {}, 'notes': {}, 'fails': {}}  # by[формат] = True/False; формат = (кодек, pix_fmt)
GLOCK = threading.Lock()
FAST = {'on': True, 'bad': 0, 'said': False}  # on — кадры берутся пачками; bad — пачки, не давшие ни кадра
JLOCK = threading.Lock()
STOP = threading.Event()
PROCS = set()
PLOCK = threading.Lock()
WORKDIRS = set()  # временные папки заданий: чистятся и при выходе по Ctrl+C


def cleanup_work():
    for w in list(WORKDIRS):
        shutil.rmtree(w, ignore_errors=True)
        WORKDIRS.discard(w)


atexit.register(cleanup_work)

# без окна консоли и с пониженным приоритетом, чтобы компьютер оставался отзывчивым
POPEN_EXTRA = {'creationflags': 0x08000000 | 0x00004000} if os.name == 'nt' else {}
NICE = ['nice', '-n', '10'] if os.name != 'nt' and shutil.which('nice') else []


def find_font(hint=None):
    cands = [hint] if hint else []
    if os.name == 'nt':
        d = os.path.join(os.environ.get('WINDIR', r'C:\Windows'), 'Fonts')
        # Verdana (как DejaVu Sans в образце) — первой: у неё такие же широкие цифры
        cands += [os.path.join(d, n) for n in ('verdana.ttf', 'tahoma.ttf', 'segoeui.ttf', 'arial.ttf', 'calibri.ttf')]
    elif sys.platform == 'darwin':
        cands += ['/System/Library/Fonts/Supplemental/Verdana.ttf', '/Library/Fonts/Verdana.ttf',
                  '/System/Library/Fonts/Supplemental/Arial.ttf', '/Library/Fonts/Arial.ttf',
                  '/System/Library/Fonts/Helvetica.ttc']
    else:
        cands += ['/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf',
                  '/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf',
                  '/usr/share/fonts/dejavu/DejaVuSans.ttf', '/usr/share/fonts/TTF/DejaVuSans.ttf',
                  '/usr/share/fonts/noto/NotoSans-Regular.ttf']
    return next((c for c in cands if c and os.path.isfile(c)), '')


def detect_ff(hint=None, font=None):
    """Найти ffmpeg и ffprobe, проверить версию и наличие drawtext (подписи на кадрах)."""
    ext = '.exe' if os.name == 'nt' else ''
    ffmpeg = ''
    if hint:
        h = os.path.join(hint, 'ffmpeg' + ext) if os.path.isdir(hint) else hint
        ffmpeg = h if os.path.isfile(h) else ''
    if not ffmpeg:  # переносимый вариант: ffmpeg лежит рядом с программой (или в её подпапке ffmpeg, ffmpeg\\bin, bin)
        for sub in ('', 'ffmpeg', os.path.join('ffmpeg', 'bin'), 'bin'):
            cand = os.path.join(base_dir(), sub, 'ffmpeg' + ext)
            if os.path.isfile(cand):
                ffmpeg = cand
                break
    ffmpeg = ffmpeg or shutil.which('ffmpeg') or ''
    ffprobe = ''
    if ffmpeg:
        sib = os.path.join(os.path.dirname(ffmpeg), 'ffprobe' + ext)
        ffprobe = sib if os.path.isfile(sib) else (shutil.which('ffprobe') or '')
    FF.update(ok=False, ffmpeg=ffmpeg, ffprobe=ffprobe, version='', drawtext=False, font=find_font(font))
    if not (ffmpeg and ffprobe):
        return
    try:
        rc, out, _ = run([ffmpeg, '-version'], capture=True, timeout=20)
        if rc != 0:
            return
        FF['version'] = (out.splitlines() or [''])[0].replace('ffmpeg version ', '').split(' Copyright')[0].strip()
        rc, out, _ = run([ffmpeg, '-hide_banner', '-filters'], capture=True, timeout=20)
        FF['drawtext'] = ' drawtext ' in out
        FF['ok'] = True
        # видеокарта NVIDIA: если ffmpeg умеет создать устройство CUDA, декодировать можно на ней
        GPU['avail'] = GPU['mode'] != 'off' and run(
            [ffmpeg, '-hide_banner', '-loglevel', 'error', '-init_hw_device', 'cuda=cu', '-f', 'lavfi',
             '-i', 'color=c=black:s=64x64:d=0.04', '-frames:v', '1', '-f', 'null', '-'], timeout=40)[0] == 0
    except (OSError, Fail, Cancelled):
        pass


def ff_info():
    return {'ok': FF['ok'], 'version': FF['version'], 'drawtext': bool(FF['drawtext'] and FF['font'])}


def gpu_info():
    """Одной строкой: чем декодируется видео при создании превью."""
    if GPU['mode'] == 'off':
        return 'процессор (--gpu off)'
    if not GPU['avail']:
        return 'процессор (видеокарта NVIDIA с CUDA не найдена)'
    if GPU['mode'] == 'on':
        bad = sorted(k[0] for k, v in GPU['by'].items() if not v)
        return 'видеокарта NVIDIA (NVDEC)' + (('; для %s отключена после сбоев' % ', '.join(bad)) if bad else '')
    return ('процессор (видеокарта NVIDIA найдена, но для превью она не ускоряет: время уходит на запуск ffmpeg '
            'и чтение файла, а не на декодирование; --gpu on включает её)')


def last_line(text):
    lines = [l.strip() for l in (text or '').splitlines() if l.strip()]
    return (lines[-1] if lines else 'нет подробностей')[:220]


def run(cmd, cwd=None, timeout=180, capture=False):
    """Запустить внешнюю программу; при остановке задания процесс убивается."""
    if STOP.is_set():
        raise Cancelled()
    p = subprocess.Popen(NICE + cmd, cwd=cwd, stdin=subprocess.DEVNULL,
                         stdout=subprocess.PIPE if capture else subprocess.DEVNULL,
                         stderr=subprocess.PIPE, **POPEN_EXTRA)
    with PLOCK:
        PROCS.add(p)
    try:
        try:
            out, err = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            p.kill()
            p.communicate()
            raise Fail('ffmpeg завис и был остановлен (дольше %d с)' % timeout)
    finally:
        with PLOCK:
            PROCS.discard(p)
    if STOP.is_set():
        raise Cancelled()
    return p.returncode, (out or b'').decode('utf-8', 'replace'), (err or b'').decode('utf-8', 'replace')


def probe(video, runner=None):
    rc, out, err = (runner or run)([FF['ffprobe'], '-v', 'error', '-print_format', 'json', '-show_format',
                        '-show_streams', video], capture=True, timeout=90)
    if rc != 0:
        raise Fail('ffprobe не смог прочитать файл: ' + last_line(err).replace(video + ': ', ''))
    try:
        data = json.loads(out)
    except ValueError:
        raise Fail('ffprobe вернул непонятный ответ')
    streams = data.get('streams') or []
    vs = next((s for s in streams if s.get('codec_type') == 'video'
               and not (s.get('disposition') or {}).get('attached_pic')), None)
    if vs is None:
        raise Fail('в файле нет видеопотока')
    au = next((s for s in streams if s.get('codec_type') == 'audio'), None)
    fmt = data.get('format') or {}
    dur = 0.0
    for v in (fmt.get('duration'), vs.get('duration')):
        try:
            dur = float(v)
        except (TypeError, ValueError):
            continue
        if dur > 0:
            break
    fps, bdelay = '', 0.0
    try:
        a, b = (vs.get('avg_frame_rate') or '0/1').split('/')
        if float(b) and float(a):
            fps = ('%.2f' % (float(a) / float(b))).rstrip('0').rstrip('.')
            bdelay = int(vs.get('has_b_frames') or 0) * float(b) / float(a)
    except (ValueError, ZeroDivisionError, TypeError):
        pass
    try:
        start = float(fmt.get('start_time') or 0)
    except (TypeError, ValueError):
        start = 0.0
    return {'duration': dur, 'start': start, 'bdelay': min(bdelay, 1.0), 'w': int(vs.get('width') or 0), 'h': int(vs.get('height') or 0),
            'vcodec': vs.get('codec_name') or '?', 'pix': vs.get('pix_fmt') or '', 'acodec': (au or {}).get('codec_name') or '', 'fps': fps}


def hms(sec):
    sec = int(sec)
    return '%d:%02d:%02d' % (sec // 3600, sec % 3600 // 60, sec % 60)


def human_size(n):
    n = float(n)
    for unit in ('Б', 'КБ', 'МБ', 'ГБ'):
        if n < 1024:
            return ('%d %s' % (n, unit)) if unit == 'Б' else ('%.1f %s' % (n, unit)).replace('.', ',')
        n /= 1024
    return ('%.1f ТБ' % n).replace('.', ',')


def preview_path(g):
    """Куда класть превью: рядом с видео, а при отдельной папке превью — в той же подпапке там."""
    base = g['name'] + '.jpg'
    if PROOT == VROOT:
        return os.path.join(os.path.dirname(g['v'][0][0]), base)
    d = os.path.join(PROOT, *g['dir'].split('/')) if g['dir'] else PROOT
    os.makedirs(d, exist_ok=True)
    return os.path.join(d, base)


def sheet_grid(info):
    """Сетка листа для этого видео: столбцы, строки, размер шрифта и высота шапки. Её же страница берёт при обрезке."""
    d = info['duration']
    cols, rows = OPTS['cols'], OPTS['rows']
    if info['h'] > info['w'] * 1.1:  # вертикальное видео: вдвое больше столбцов и вдвое меньше строк
        cols, rows = rows * 2, -(-cols // 2)
    if d < cols * rows:              # короткий ролик — меньше кадров
        rows = max(1, int(d // cols))
    fs_h = max(14, OPTS['width'] // 80)
    hh = 3 * (fs_h + 8) + 28 if FF['drawtext'] and FF['font'] and OPTS['header'] else 0
    return cols, rows, fs_h, hh


def use_gpu(video, info):
    """Видеокарта используется только с --gpu on. Для одного ключевого кадра она не быстрее процессора."""
    if GPU['mode'] != 'on' or not GPU['avail']:
        return False
    key = (info['vcodec'], info.get('pix', ''))
    GPU['by'].setdefault(key, True)
    return GPU['by'][key]


def extract_batch(video, jr, work, idx, times, tw, text, fs, hw):
    """Взять сразу много кадров одним запуском ffmpeg. Возвращает (номера готовых кадров, текст ошибки).

    Запуск ffmpeg.exe в Windows дорог (сотни миллисекунд вместе с проверкой антивирусом), а кадров на лист 90:
    раньше это было 90 запусков на видео, теперь около трёх. Каждый кадр — отдельный вход с перемоткой -ss
    и отдельный выход; декодер на вход один поток, потому что нужен всего один ключевой кадр.
    """
    cmd = [FF['ffmpeg'], '-hide_banner', '-loglevel', 'error', '-nostdin', '-y']
    chains, outs = [], []
    for k, (i, t) in enumerate(zip(idx, times)):
        if hw:
            cmd += ['-hwaccel', 'cuda']
        cmd += ['-threads', '1', '-noaccurate_seek', '-ss', '%.3f' % t, '-i', video]
        c = '[%d:v:0]scale=%d:-2:flags=area' % (k, tw)
        if text:
            c += (",drawtext=fontfile=font.ttf:text='%%{pts\\:gmtime\\:%.3f\\:%%T}':fontsize=%d"
                  ":fontcolor=white:box=1:boxcolor=black@0.5:boxborderw=2:x=w-tw-5:y=h-th-4") % (t, fs)
        chains.append(c + '[o%d]' % k)
        outs += ['-map', '[o%d]' % k, '-frames:v', '1', '%s/f%02d.png' % (jr, i)]
    cmd += ['-filter_complex', ';'.join(chains)] + outs
    rc, _o, err = run(cmd, cwd=work, timeout=300)
    done = [i for i in idx if os.path.exists(os.path.join(work, jr, 'f%02d.png' % i))]
    if len(done) == len(idx):
        return done, ''
    return done, err or ('ffmpeg завершился с кодом %d' % rc)


def make_preview(g, work, jid, redo=False):
    """Лист кадров: сетка cols×rows, между кадрами тонкие линии, в углу каждого кадра время.

    Кадры берутся равномерно от начала (первый — на 00:00:00). Заголовок с данными о файле — только с --header.
    redo=True: старые превью уходят в _на_удаление, а на их место кладётся новое.
    """
    video = g['v'][0][0]
    final = preview_path(g)
    old = list(g['p']) if redo else []
    if not redo and os.path.exists(final):
        raise Fail('файл превью уже существует: ' + os.path.basename(final))
    info = probe(video)
    d = info['duration']
    if d <= 0:
        raise Fail('не удалось определить длительность видео')
    hw = use_gpu(video, info)
    gkey = (info['vcodec'], info.get('pix', ''))
    cols, rows, fs_h, hh = sheet_grid(info)
    n = cols * rows
    width, gap = OPTS['width'], 1
    tw = (width - (cols - 1) * gap) // cols
    text = bool(FF['drawtext'] and FF['font'])
    jr = 'j%d' % jid                 # пути внутри ffmpeg — относительные от work: без двоеточий и обратных слэшей
    jd = os.path.join(work, jr)
    os.makedirs(jd, exist_ok=True)
    try:
        got, last_err = set(), ''
        fs_ts = max(9, round(tw * 0.047))
        times = [d * i / n for i in range(n)]
        # быстрый путь: кадры берутся пачками, одним запуском ffmpeg на ~30 кадров (а не 90 запусков на лист)
        per = cols * max(1, 30 // cols)
        per = max(1, min(per, 26000 // (len(video) + 380)))  # командная строка Windows — не длиннее 32 767 знаков
        if FAST['on']:
            for s0 in range(0, n, per):
                idx = list(range(s0, min(n, s0 + per)))
                done, err = extract_batch(video, jr, work, idx, [times[i] for i in idx], tw, text, fs_ts, hw)
                got.update(done)
                if err:
                    last_err = err
                if not done:  # пачка не дала ни одного кадра: дальше пачками не пробуем, остальное доберёт медленный путь
                    with GLOCK:
                        FAST['bad'] += 1
                        if FAST['bad'] >= 3 and FAST['on']:
                            FAST['on'] = False
                            print('Быстрый рендер отключён (%s). Кадры берутся по одному: это медленнее.' % last_line(err))
                    break
            if got and not FAST['said']:
                FAST['said'] = True
                print('Рендер превью: кадры берутся пачками, около %d за один запуск ffmpeg.' % per)
        for i in range(n):  # недостающие кадры (пачка не сработала, перемотка в «дыру» и т. п.) — по одному, как раньше
            if i in got:
                continue
            t = times[i]
            # попытки: на видеокарте (если выбрана) → на процессоре → на процессоре с точной перемоткой чуть раньше
            for attempt in ((0, 1, 2) if hw else (1, 2)):
                tt = t if attempt < 2 else max(0.0, t - 3.0)
                vf = 'scale=%d:-2:flags=area' % tw  # area вдвое быстрее bicubic и для уменьшения не хуже
                if text:
                    # метка — реальное время кадра (pts + смещение перемотки) на тёмной плашке в правом нижнем углу
                    vf += (",drawtext=fontfile=font.ttf:text='%%{pts\\:gmtime\\:%.3f\\:%%T}':fontsize=%d"
                           ":fontcolor=white:box=1:boxcolor=black@0.5:boxborderw=2:x=w-tw-5:y=h-th-4") % (tt, fs_ts)
                cmd = [FF['ffmpeg'], '-hide_banner', '-loglevel', 'error', '-nostdin', '-y']
                if attempt == 0:
                    cmd += ['-hwaccel', 'cuda']
                if attempt < 2:
                    cmd.append('-noaccurate_seek')  # ближайший ключевой кадр: быстро и читает мало данных
                cmd += ['-ss', '%.3f' % tt, '-i', video, '-frames:v', '1', '-an', '-sn', '-dn',
                        '-vf', vf, '%s/f%02d.png' % (jr, i)]
                rc, _o, err = run(cmd, cwd=work)
                if rc == 0 and os.path.exists(os.path.join(jd, 'f%02d.png' % i)):
                    got.add(i)
                    break
                last_err = err or last_err
                if attempt == 0:  # видеокарта подвела: три сбоя подряд на этом формате — дальше только процессор
                    with GLOCK:
                        GPU['fails'][gkey] = GPU['fails'].get(gkey, 0) + 1
                        if GPU['fails'][gkey] >= 3 and GPU['by'].get(gkey):
                            GPU['by'][gkey] = False
                            print('Декодирование %s/%s: видеокарта отключена после сбоев, дальше процессор' % (gkey[0], gkey[1] or '?'))
                    hw = GPU['by'].get(gkey, False)
        got = sorted(got)
        if len(got) < max(2, n // 3):
            raise Fail('не удалось извлечь кадры: ' + last_line(last_err))
        for k, i in enumerate(got):
            os.replace(os.path.join(jd, 'f%02d.png' % i), os.path.join(jd, 's%02d.png' % k))
        rows2 = -(-len(got) // cols)
        bg = '0x1c1c1c'
        vf2 = 'tile=%dx%d:margin=0:padding=%d:color=%s,pad=%d:ih:0:0:color=%s' % (cols, rows2, gap, bg, width, bg)
        if hh:
            name = os.path.basename(video)
            if len(name) > 110:
                name = name[:60] + '…' + name[-45:]
            try:
                size = os.path.getsize(video)
            except OSError:
                size = 0
            lines = [name,
                     'Размер: %s    Длительность: %s' % (human_size(size), hms(d)),
                     'Видео: %s, %dx%d%s    Аудио: %s' % (info['vcodec'], info['w'], info['h'],
                                                         (', %s fps' % info['fps']) if info['fps'] else '',
                                                         info['acodec'] or 'нет')]
            with open(os.path.join(jd, 'hdr.txt'), 'w', encoding='utf-8') as f:
                f.write('\n'.join(lines))
            vf2 += (',pad=iw:ih+%d:0:%d:color=%s,drawtext=fontfile=font.ttf:textfile=%s/hdr.txt:expansion=none'
                    ':fontsize=%d:fontcolor=white:x=16:y=16:line_spacing=8') % (hh, hh, bg, jr, fs_h)
        rc, _o, err = run([FF['ffmpeg'], '-hide_banner', '-loglevel', 'error', '-nostdin', '-y',
                           '-framerate', '1', '-i', '%s/s%%02d.png' % jr, '-vf', vf2,
                           '-frames:v', '1', '-q:v', '3', '%s/sheet.jpg' % jr], cwd=work)
        sheet = os.path.join(jd, 'sheet.jpg')
        if rc != 0 or not os.path.exists(sheet) or os.path.getsize(sheet) == 0:
            raise Fail('не удалось собрать лист: ' + last_line(err))
        part = final + '.part'
        moved = []
        try:
            shutil.copyfile(sheet, part)
            for path, root, *_ in old:  # прежние превью не пропадают, а лежат в _на_удаление до очистки
                moved.append((path, to_trash(path, root)))
            os.replace(part, final)
            tstat_add(len(moved), sum(f[2] for f in old))
        except OSError as e:
            for src, dst in reversed(moved):
                try:
                    move(dst, src)
                except OSError:
                    pass
            try:
                os.remove(part)
            except OSError:
                pass
            raise Fail('не удалось записать превью (%s): %s' % (getattr(e, 'strerror', None) or e, final))
        return final, moved
    finally:
        shutil.rmtree(jd, ignore_errors=True)


def worker(q, work, redo=False):
    while not STOP.is_set():
        try:
            gid = q.get_nowait()
        except queue.Empty:
            return
        with LOCK:
            g = GROUPS.get(gid)
        if g is None or not g['v'] or (g['p'] and not redo):
            with JLOCK:
                JOB['done'] += 1
            continue
        name = os.path.basename(g['v'][0][0])
        with JLOCK:
            JOB['active'][gid] = name
        err = None
        hook = AFTER.pop(gid, None)
        try:
            out, moved = make_preview(g, work, gid, redo)
            st = os.stat(out)
            with LOCK:
                g['p'][:] = [(out, PROOT, st.st_size, st.st_mtime)]
                if hook:
                    hook(out, moved)
        except Cancelled:
            with JLOCK:
                JOB['active'].pop(gid, None)
            return
        except Fail as e:
            err = str(e)
        except Exception as e:  # noqa: BLE001 — одна поломка не должна останавливать всю очередь
            err = '%s: %s' % (type(e).__name__, e)
        with JLOCK:
            JOB['active'].pop(gid, None)
            JOB['done'] += 1
            if err:
                JOB['failed'][gid] = err
            else:
                JOB['ok'] += 1
            done, total = JOB['done'], JOB['total']
        print('[%d/%d] %s: %s' % (done, total, 'ОШИБКА' if err else ('пересоздано' if redo else 'создано'), err or name))


def finish(threads, work):
    for t in threads:
        t.join()
    shutil.rmtree(work, ignore_errors=True)
    WORKDIRS.discard(work)
    with JLOCK:
        JOB['running'] = False
        JOB['stopped'] = STOP.is_set()
        ok, failed = JOB['ok'], len(JOB['failed'])
    print('Создание превью %s: создано %d, ошибок %d' % ('остановлено' if STOP.is_set() else 'завершено', ok, failed))


def start_job(ids, redo=False):
    if not FF['ok']:
        raise Fail('ffmpeg не найден: создавать превью нечем. Установите ffmpeg или укажите --ffmpeg ПУТЬ')
    with LOCK:
        todo = [i for i in dict.fromkeys(ids)
                if isinstance(i, int) and i in GROUPS and GROUPS[i]['v'] and (redo or not GROUPS[i]['p'])]
    if not todo:
        raise Fail('нечего пересоздавать: у выбранных превью нет видео' if redo
                   else 'нечего создавать: у выбранных видео уже есть превью')
    with JLOCK:
        if JOB['running']:
            raise Fail('создание превью уже идёт', 409)
        with CLOCK:
            if CUT['running']:
                raise Fail('идёт обрезка видео: дождитесь её конца', 409)
        JOB.update(running=True, stopped=False, redo=bool(redo), total=len(todo), done=0, ok=0,
                   failed={}, active={}, started=time.time())
    STOP.clear()
    try:
        work = tempfile.mkdtemp(prefix='pairview_')
        WORKDIRS.add(work)
        if FF['drawtext'] and FF['font']:
            shutil.copyfile(FF['font'], os.path.join(work, 'font.ttf'))
    except OSError as e:
        with JLOCK:
            JOB['running'] = False
        raise Fail('не удалось подготовить временную папку: %s' % e)
    q = queue.Queue()
    for i in todo:
        q.put(i)
    threads = [threading.Thread(target=worker, args=(q, work, redo), daemon=True)
               for _ in range(max(1, min(OPTS['jobs'], len(todo))))]
    for t in threads:
        t.start()
    threading.Thread(target=finish, args=(threads, work), daemon=True).start()
    print('%s превью: %d видео, потоков: %d' % ('Пересоздание' if redo else 'Создание', len(todo), len(threads)))


def stop_job():
    STOP.set()
    with PLOCK:
        procs = list(PROCS)
    for p in procs:
        try:
            p.kill()
        except OSError:
            pass


def job_status():
    with JLOCK:
        j = dict(JOB)
        j['failed'] = dict(JOB['failed'])
        j['active'] = list(JOB['active'].values())
        j['elapsed'] = round(time.time() - JOB['started'], 1) if JOB['started'] else 0
    j.pop('started', None)
    return j


# ───────────────────────── обрезка видео (без перекодирования) ─────────────────────────
#
# Потоки копируются как есть (-c copy): быстро и без потерь, но оставляемый кусок может начинаться только с ключевого
# кадра. Поэтому начало каждого оставляемого куска сдвигается НАЗАД к ключевому кадру (key_before): лишнего может
# остаться до пары секунд, нужное не теряется. Все куски собираются одним запуском ffmpeg (concat с inpoint/outpoint),
# результат пишется рядом как .part и проверяется по длительности; только потом оригинал уходит в _на_удаление,
# а обрезанный файл встаёт на его место. Ctrl+Z возвращает оригинал и прежнее превью.

CUT = {'running': False, 'id': None, 'name': '', 'stage': '', 'pct': 0, 'error': '', 'note': '', 'stopped': False}
CLOCK = threading.Lock()
CUTPROC = {'p': None}
AFTER = {}    # номер пары -> функция(новое превью, [(старое, куда перенесено)]): её вызывает worker после пересоздания
PROBES = {}   # (путь, размер, mtime) -> данные ffprobe: при обрезке их спрашивают часто
MUXERS = {'.mp4': 'mp4', '.m4v': 'mp4', '.mov': 'mov', '.mkv': 'matroska', '.webm': 'webm', '.avi': 'avi',
          '.flv': 'flv', '.wmv': 'asf', '.mpg': 'mpeg', '.mpeg': 'mpeg', '.vob': 'vob', '.ts': 'mpegts',
          '.m2ts': 'mpegts', '.3gp': '3gp', '.ogv': 'ogg'}


def ff_call(cmd, capture=True, timeout=60, raw=False):
    """Короткий запуск ffmpeg/ffprobe для обрезки (не зависит от остановки очереди превью). Ответ — как у run()."""
    try:
        p = subprocess.run(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=timeout, **POPEN_EXTRA)
    except subprocess.TimeoutExpired:
        raise Fail('ffmpeg не ответил за %d с' % timeout, 500)
    except OSError as e:
        raise Fail('ffmpeg не запустился: %s' % e, 500)
    out = p.stdout if raw else p.stdout.decode('utf-8', 'replace')
    return p.returncode, out, p.stderr.decode('utf-8', 'replace')


def cut_target(gid):
    with LOCK:
        g = GROUPS.get(gid)
    if g is None:
        raise Gone('пары уже нет — список обновлён')
    if not g['v']:
        raise Fail('у этого превью нет видео')
    if len(g['v']) > 1:
        raise Fail('у пары несколько видеофайлов с одним именем: непонятно, какой обрезать')
    if not FF['ok']:
        raise Fail('ffmpeg не найден: обрезать нечем. Установите ffmpeg или укажите --ffmpeg ПУТЬ')
    return g, g['v'][0][0]


def cut_probe(video):
    try:
        st = os.stat(video)
    except OSError as e:
        raise Fail('видео недоступно: %s' % (getattr(e, 'strerror', None) or e), 404)
    key = (video, st.st_size, st.st_mtime)
    info = PROBES.get(key)
    if info is None:
        info = probe(video, ff_call)
        if info['duration'] <= 0:
            raise Fail('не удалось определить длительность видео')
        if len(PROBES) > 50:
            PROBES.clear()
        PROBES[key] = info
    return info


def cut_info(gid):
    """Данные для таймлайна: длительность и сетка листа превью (по ней страница показывает кадр мгновенно)."""
    g, video = cut_target(gid)
    if os.path.splitext(video)[1].lower() not in MUXERS:
        raise Fail('файлы %s обрезать не умею' % os.path.splitext(video)[1])
    info = cut_probe(video)
    cols, rows, _fs, hh = sheet_grid(info)
    return {'id': gid, 'duration': info['duration'], 'w': info['w'], 'h': info['h'],
            'cols': cols, 'rows': rows, 'hh': hh, 'width': OPTS['width'], 'file': os.path.basename(video)}


def key_before(video, info, t):
    """Время ближайшего ключевого кадра не позже t (секунды от начала видео)."""
    if t <= 0.05:
        return 0.0
    st = info['start']
    for back in (8, 40, 240):
        a = max(0.0, t - back)
        rc, out, err = ff_call([FF['ffprobe'], '-v', 'error', '-select_streams', 'v:0',
                                '-read_intervals', '%.3f%%%.3f' % (st + a, st + t + 0.5),
                                '-show_entries', 'packet=pts_time,flags', '-of', 'compact=p=0', video], timeout=90)
        if rc != 0:
            raise Fail('ffprobe не прочитал файл: ' + last_line(err), 500)
        best = None
        for line in out.splitlines():
            f = dict(x.split('=', 1) for x in line.strip().split('|') if '=' in x)
            if 'K' not in f.get('flags', ''):
                continue
            try:
                pt = float(f.get('pts_time', '')) - st
            except ValueError:
                continue
            if pt <= t + 0.0005 and (best is None or pt > best):
                best = pt
        if best is not None:
            return max(0.0, best)
        if a <= 0:
            break
    return 0.0


def cut_key(gid, t):
    g, video = cut_target(gid)
    info = cut_probe(video)
    return {'t': key_before(video, info, min(max(0.0, float(t)), info['duration']))}


def cut_frame(gid, t, width):
    """Точный кадр в момент t (JPEG) — для всплывающей подсказки над таймлайном."""
    g, video = cut_target(gid)
    width = max(160, min(int(width), 960))
    rc, out, err = ff_call([FF['ffmpeg'], '-hide_banner', '-loglevel', 'error', '-nostdin',
                            '-ss', '%.3f' % max(0.0, float(t)), '-i', video, '-frames:v', '1', '-an', '-sn', '-dn',
                            '-vf', 'scale=%d:-2' % width, '-f', 'image2pipe', '-c:v', 'mjpeg', '-q:v', '4', 'pipe:1'],
                           timeout=60, raw=True)
    if rc != 0 or not out:
        raise Fail('кадр не получен: ' + last_line(err), 500)
    return out


def cut_regions(info, cuts):
    """Проверить и упорядочить вырезаемые куски [(начало, конец)]."""
    if not isinstance(cuts, list):
        raise Fail('не удалось разобрать запрос')
    d = info['duration']
    regs = []
    for c in cuts:
        if not (isinstance(c, list) and len(c) == 2 and all(isinstance(x, (int, float)) for x in c)):
            raise Fail('не удалось разобрать запрос')
        a, b = max(0.0, min(c)), min(d, max(c))
        if b - a >= 0.05:
            regs.append([a, b])
    if not regs:
        raise Fail('не отмечено, что вырезать')
    regs.sort()
    return regs


def cut_plan(video, info, regs):
    """Вырезаемые куски -> оставляемые [(начало, конец)], начало каждого — на ключевом кадре."""
    d = info['duration']
    keep, pos = [], 0.0
    for a, b in regs:
        if a - pos > 0.05:
            keep.append([pos, a])
        pos = max(pos, b)
    if d - pos > 0.05:
        keep.append([pos, d])
    plan = []
    for a, b in keep:
        a = key_before(video, info, a) if a > 0 else 0.0
        if plan and a <= plan[-1][1] + 0.01:  # ключевой кадр попал в предыдущий кусок: куски сливаются
            plan[-1][1] = max(plan[-1][1], b)
        else:
            plan.append([a, b])
    total = sum(b - a for a, b in plan)
    if total < 1:
        raise Fail('от видео ничего не останется')
    if d - total < 0.5:
        raise Fail('вырезать нечего: куски короче расстояния между ключевыми кадрами')
    return plan, total


def cut_status():
    with CLOCK:
        return dict(CUT)


def cut_start(gid, cuts):
    g, video = cut_target(gid)
    fmt = MUXERS.get(os.path.splitext(video)[1].lower())
    if not fmt:
        raise Fail('файлы %s обрезать не умею' % os.path.splitext(video)[1])
    regs = cut_regions(cut_probe(video), cuts)
    if regs[0][0] <= 0.05 and regs[-1][1] >= cut_probe(video)['duration'] - 0.05 and len(regs) == 1:
        raise Fail('от видео ничего не останется')
    with JLOCK:
        if JOB['running']:
            raise Fail('идёт создание превью: обрезать можно после него', 409)
        with CLOCK:
            if CUT['running']:
                raise Fail('уже идёт обрезка другого видео', 409)
            CUT.update(running=True, id=gid, name=os.path.basename(video), stage='подготовка', pct=0,
                       error='', note='', stopped=False)
    threading.Thread(target=cut_worker, args=(gid, g, video, fmt, regs), daemon=True).start()
    return cut_status()


def cut_stop():
    with CLOCK:
        if CUT['running']:
            CUT['stopped'] = True
        p = CUTPROC['p']
    if p is not None:
        try:
            p.kill()
        except OSError:
            pass
    return cut_status()


def cut_run(cmd, total, err_path):
    """ffmpeg с ходом выполнения (-progress): процент — по времени уже записанного."""
    with open(err_path, 'wb') as ef:
        p = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=ef, **POPEN_EXTRA)
        with CLOCK:
            CUTPROC['p'] = p
            stopped = CUT['stopped']
        if stopped:
            p.kill()
        try:
            for line in p.stdout:
                if line.startswith(b'out_time_us=') or line.startswith(b'out_time_ms='):
                    try:
                        sec = int(line.split(b'=', 1)[1]) / 1e6
                    except ValueError:
                        continue
                    with CLOCK:
                        CUT['pct'] = max(0, min(99, int(100 * sec / total)))
            rc = p.wait()
        finally:
            with CLOCK:
                CUTPROC['p'] = None
    with open(err_path, encoding='utf-8', errors='replace') as ef:
        return rc, ef.read()


def cut_worker(gid, g, video, fmt, regs):
    work = tempfile.mkdtemp(prefix='pairview_cut_')
    WORKDIRS.add(work)
    part = video + '.part'
    err = ''
    try:
        info = cut_probe(video)
        with CLOCK:
            CUT['stage'] = 'поиск ключевых кадров'
        plan, total = cut_plan(video, info, regs)
        st, d = info['start'], info['duration']
        lines = ['ffconcat version 1.0']
        for a, b in plan:
            lines.append("file '%s'" % video.replace("'", "'\\''"))
            if a > 0:
                lines.append('inpoint %.6f' % (st + a + 0.0005))  # чуть позже ключевого кадра: округление не уведёт на прежний
            if b < d - 0.01:
                # concat сравнивает outpoint со временем декодирования (dts): у видео с B-кадрами оно отстаёт от
                # времени показа, и без поправки в кусок попадают лишние кадры, а на стыке время кадров совпадает
                lines.append('outpoint %.6f' % (st + max(a + 0.04, b - info['bdelay'])))
                lines.append('duration %.6f' % (b - a))  # иначе следующий кусок встанет раньше конца этого (на ту же задержку)
        lst = os.path.join(work, 'list.txt')
        with open(lst, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines) + '\n')
        with CLOCK:
            CUT['stage'] = 'обрезка'
        cmd = [FF['ffmpeg'], '-hide_banner', '-loglevel', 'error', '-nostdin', '-y', '-f', 'concat', '-safe', '0',
               '-i', lst, '-map', '0:v:0', '-map', '0:a?', '-c', 'copy', '-avoid_negative_ts', 'make_zero',
               '-progress', 'pipe:1', '-nostats', '-f', fmt, part]
        print('Обрезка %s: оставляю %s' % (os.path.basename(video), ', '.join('%s–%s' % (hms(a), hms(b)) for a, b in plan)))
        rc, ferr = cut_run(cmd, total, os.path.join(work, 'err.txt'))
        if cut_status()['stopped']:
            raise Fail('обрезка остановлена, видео не изменено')
        if rc != 0 or not os.path.exists(part) or os.path.getsize(part) == 0:
            raise Fail('ffmpeg не смог обрезать: ' + last_line(ferr))
        new = probe(part, ff_call)
        if abs(new['duration'] - total) > max(3.0, total * 0.02):
            raise Fail('у результата длительность %s вместо %s — видео не изменено' % (hms(new['duration']), hms(total)))
        with CLOCK:
            CUT.update(stage='замена файла', pct=100)
        with LOCK:
            if GROUPS.get(gid) is not g or not g['v'] or g['v'][0][0] != video:
                raise Fail('пару удалили или переименовали, пока шла обрезка — видео не изменено')
            snap = dict(g, v=list(g['v']), p=list(g['p']))  # прежнее состояние пары — для Ctrl+Z
        root, old_size = g['v'][0][1], g['v'][0][2]
        try:
            trash_v = to_trash(video, root)
        except OSError as e:
            raise Fail(explain(MoveError(video, e)), 409)
        try:
            os.replace(part, video)
        except OSError as e:
            try:
                move(trash_v, video)
            except OSError:
                pass
            raise Fail('не удалось записать обрезанное видео: %s' % (getattr(e, 'strerror', None) or e))
        tstat_add(1, old_size)
        PROBES.clear()
        s2 = os.stat(video)
        rec = (gid, snap, [(video, trash_v)], [(video, root)])  # отмена: обрезанный — в корзину, оригинал — на место
        with LOCK:
            g['v'][:] = [(video, root, s2.st_size, s2.st_mtime)]
            UNDO.append([rec])
        print('Обрезано: %s, было %s, стало %s' % (os.path.basename(video), hms(d), hms(new['duration'])))
    except Fail as e:
        err = str(e)
    except Exception as e:  # noqa: BLE001
        err = '%s: %s' % (type(e).__name__, e)
    finally:
        try:
            if os.path.exists(part):
                os.remove(part)
        except OSError:
            pass
        shutil.rmtree(work, ignore_errors=True)
        WORKDIRS.discard(work)
        with CLOCK:
            CUT.update(running=False, error=err, stage='' if err else 'готово')
    if err:
        print('Обрезка %s: %s' % (os.path.basename(video), err))
        return

    def after(out, moved):  # старое превью ушло в корзину, новое встало: отмена должна вернуть старое
        rec[2].extend(moved)
        rec[3].append((out, PROOT))

    AFTER[gid] = after
    try:
        start_job([gid], redo=bool(g['p']))
    except Fail as e:
        AFTER.pop(gid, None)
        with CLOCK:
            CUT['note'] = 'превью не пересоздано (%s): сделайте это кнопкой «Пересоздать превью»' % e


# ───────────────────────── смена открытой папки ─────────────────────────

WIN = {'window': None}       # окно pywebview, если программа открыта в своём окне
PICKLOCK = threading.Lock()  # не больше одного диалога выбора папки


def ask_folder(initial=''):
    """Диалог выбора папки: в своём окне — диалог самого окна, в браузере — tkinter. Пусто — отменён."""
    w = WIN['window']
    if w is not None:
        try:
            import webview
            kind = getattr(getattr(webview, 'FileDialog', None), 'FOLDER', None)
            if kind is None:
                kind = webview.FOLDER_DIALOG
            r = w.create_file_dialog(kind, directory=initial or '')
            if isinstance(r, (list, tuple)):
                r = r[0] if r else ''
            return r or ''
        except Exception as e:  # noqa: BLE001 — не вышло диалогом окна: пробуем tkinter
            print('Диалог окна не открылся (%s: %s), открываю обычный.' % (type(e).__name__, e))
    return pick_folder(initial)


def switch_root(folder, previews=''):
    """Открыть другую папку без перезапуска программы.

    Пока создаются превью, нельзя: ffmpeg пишет в старую папку. Стек отмены очищается: удалённое в старой папке
    остаётся в её _на_удаление. Номера пар продолжаются (не начинаются с нуля): картинки /p/<id> кешируются браузером.
    """
    global VROOT, PROOT, ROOT_NAME
    vroot = os.path.abspath(folder)
    proot = os.path.abspath(previews) if previews else vroot
    for r in (vroot, proot):
        if not os.path.isdir(r):
            raise Fail('папка недоступна: %s' % r, 404)
    busy = 'идёт создание превью: дождитесь конца или остановите его'
    with ROOTLOCK:
        with JLOCK:
            if JOB['running']:
                raise Fail(busy, 409)
        with CLOCK:
            if CUT['running']:
                raise Fail('идёт обрезка видео: дождитесь её конца', 409)
        ignored = SCAN['ignored']
        groups = scan(vroot, proot)
        if not groups:
            n, SCAN['ignored'] = SCAN['ignored'], ignored
            raise Fail('в папке %s нет ни видео, ни превью' % vroot +
                       (' (видеофайлы %d шт. игнорируются: --ignore-ext)' % n if n else ''), 404)
        with LOCK, JLOCK:
            if JOB['running']:
                raise Fail(busy, 409)
            GROUPS.clear()
            UNDO.clear()
            for key in sorted(groups):
                GROUPS[new_id()] = groups[key]
            VROOT, PROOT = vroot, proot
            ROOT_NAME = os.path.basename(vroot) or vroot
            JOB.update(stopped=False, total=0, done=0, ok=0, failed={})  # ошибки прежней папки к новой не относятся
    remember_folder(vroot, proot)
    refresh_trash_stats()
    w = WIN['window']
    if w is not None:
        try:
            w.set_title('Video Manager — ' + ROOT_NAME)
        except Exception:  # noqa: BLE001
            pass
    print('Открыта папка: %s%s, пар: %d' % (vroot, '' if proot == vroot else ' (превью: %s)' % proot, len(groups)))
    return {'ok': True, 'root': ROOT_NAME}


def choose_root(folder=None):
    """Кнопка в шапке: folder — из списка недавних (другие пути с клиента не принимаются), None — диалог выбора."""
    if folder is not None:
        previews = recent_previews(folder)
        if previews is None:
            raise Fail('этой папки нет в списке недавних')
        return switch_root(folder, previews)
    if not PICKLOCK.acquire(blocking=False):
        raise Fail('окно выбора папки уже открыто', 409)
    try:
        path = ask_folder(VROOT)
    finally:
        PICKLOCK.release()
    if not path:
        return {'ok': False}
    previews = recent_previews(path)
    return switch_root(path, previews or '')


# ───────────────────────── HTTP ─────────────────────────

MAX_BODY = 4 * 1024 * 1024


class Handler(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'

    def log_message(self, *args):
        pass

    def reply(self, code, body, ctype='application/json; charset=utf-8'):
        if not isinstance(body, bytes):
            body = json.dumps(body, ensure_ascii=False).encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Referrer-Policy', 'no-referrer')
        self.end_headers()
        self.wfile.write(body)

    def image(self, gid):
        with LOCK:
            g = GROUPS.get(gid)
        if not g or not g['p']:
            raise LookupError('нет превью')
        path = g['p'][0][0]
        with open(path, 'rb') as f:  # читаем целиком и сразу закрываем: на время отправки файл не держится
            data = f.read()
        self.send_response(200)
        self.send_header('Content-Type', IMAGE[os.path.splitext(path)[1].lower()])
        self.send_header('Content-Length', str(len(data)))
        self.send_header('Cache-Control', 'private, max-age=3600')
        self.end_headers()
        self.wfile.write(data)

    @staticmethod
    def jbody(raw):
        try:
            v = json.loads(raw.decode('utf-8') or '{}')
        except ValueError:
            raise Fail('не удалось разобрать запрос')
        if not isinstance(v, dict):
            raise Fail('не удалось разобрать запрос')
        return v

    def do_GET(self):
        self.dispatch(False)

    def do_POST(self):
        self.dispatch(True)

    def dispatch(self, post):
        raw = b''
        if post:  # тело читаем всегда: иначе при keep-alive оно «слипнется» со следующим запросом
            try:
                n = int(self.headers.get('Content-Length') or 0)
            except ValueError:
                n = 0
            if n > MAX_BODY:
                self.close_connection = True
                return self.reply(413, {'error': 'слишком большой запрос'})
            raw = self.rfile.read(n) if n > 0 else b''
        u = urlparse(self.path)
        t = parse_qs(u.query).get('t', [''])[0]
        host = self.headers.get('Host', '').rsplit(':', 1)[0]
        # запросы принимаются только с ключом из адреса и только на локальный адрес
        if host not in ('127.0.0.1', 'localhost') or not secrets.compare_digest(t.encode(), TOKEN.encode()):
            return self.reply(403, {'error': 'нет доступа'})
        p = u.path.strip('/').split('/')
        try:
            if not post and p == ['']:
                cfg = json.dumps(load_settings(), ensure_ascii=False).replace('<', '\\u003c')
                self.reply(200, PAGE.replace('/*SETTINGS*/{}', cfg).encode('utf-8'), 'text/html; charset=utf-8')
            elif not post and p == ['api', 'list']:
                self.reply(200, listing())
            elif not post and p == ['api', 'trash']:
                self.reply(200, trash_stats())
            elif not post and p == ['api', 'make']:
                self.reply(200, job_status())
            elif not post and p[0] == 'p' and len(p) == 2:
                self.image(int(p[1]))
            elif not post and p == ['api', 'cut']:
                self.reply(200, cut_status())
            elif not post and len(p) == 4 and p[:3] == ['api', 'cut', 'frame']:
                qs = parse_qs(u.query)
                self.reply(200, cut_frame(int(p[3]), float(qs.get('at', ['0'])[0]), int(qs.get('w', ['480'])[0])),
                           'image/jpeg')
            elif post and p == ['api', 'make']:
                try:
                    body = json.loads(raw.decode('utf-8') or '{}') or {}
                    ids, redo = body.get('ids') or [], bool(body.get('redo'))
                except (ValueError, AttributeError):
                    raise Fail('не удалось разобрать запрос')
                if not isinstance(ids, list):
                    raise Fail('не удалось разобрать запрос')
                start_job(ids, redo)
                self.reply(200, job_status())
            elif post and p == ['api', 'settings']:
                save_settings(self.jbody(raw))
                self.reply(200, {'ok': True})
            elif post and p == ['api', 'mpc']:
                b = self.jbody(raw)
                if isinstance(b.get('ids'), list):
                    files = mpc_files(b['ids'])
                else:
                    files = folder_videos(str(b.get('dir') or ''), bool(b.get('deep')))
                self.reply(200, send_to_mpc(files, bool(b.get('add'))))
            elif post and p == ['api', 'delete-many']:
                ids = self.jbody(raw).get('ids')
                if not isinstance(ids, list):
                    raise Fail('не удалось разобрать запрос')
                self.reply(200, delete_batch(ids))
            elif post and p == ['api', 'explorer']:
                b = self.jbody(raw)
                gid = b.get('id')
                self.reply(200, show_in_explorer(gid=gid) if isinstance(gid, int) else show_in_explorer(rel=str(b.get('dir') or '')))
            elif post and p == ['api', 'folder', 'info']:
                self.reply(200, folder_info(str(self.jbody(raw).get('dir') or '')))
            elif post and p == ['api', 'folder', 'delete']:
                self.reply(200, delete_folder(str(self.jbody(raw).get('dir') or '')))
            elif post and p == ['api', 'empty']:
                self.reply(200, {'dirs': find_empty_dirs()})
            elif post and p == ['api', 'empty', 'delete']:
                dirs = self.jbody(raw).get('dirs')
                if not isinstance(dirs, list):
                    raise Fail('не удалось разобрать запрос')
                self.reply(200, delete_empty(dirs))
            elif post and p == ['api', 'cut', 'info']:
                self.reply(200, cut_info(int(self.jbody(raw).get('id', -1))))
            elif post and p == ['api', 'cut', 'key']:
                b = self.jbody(raw)
                self.reply(200, cut_key(int(b.get('id', -1)), float(b.get('at') or 0)))
            elif post and p == ['api', 'cut', 'start']:
                b = self.jbody(raw)
                self.reply(200, cut_start(int(b.get('id', -1)), b.get('cuts')))
            elif post and p == ['api', 'cut', 'stop']:
                self.reply(200, cut_stop())
            elif post and p == ['api', 'root', 'pick']:
                self.reply(200, choose_root())
            elif post and p == ['api', 'root', 'recent']:
                self.reply(200, choose_root(str(self.jbody(raw).get('folder') or '')))
            elif post and p == ['api', 'rescan']:
                self.reply(200, rescan())
            elif post and p == ['api', 'orphans']:
                try:
                    ids = (json.loads(raw.decode('utf-8') or '{}') or {}).get('ids') or []
                except (ValueError, AttributeError):
                    raise Fail('не удалось разобрать запрос')
                if not isinstance(ids, list):
                    raise Fail('не удалось разобрать запрос')
                self.reply(200, delete_orphans(ids))
            elif post and p == ['api', 'make', 'stop']:
                stop_job()
                self.reply(200, job_status())
            elif post and p == ['api', 'purge']:
                self.reply(200, purge())
            elif post and p == ['api', 'trash', 'open']:
                open_trash()
                self.reply(200, {'ok': True})
            elif post and p == ['api', 'undo']:
                self.reply(200, {'id': undo_last(), 'trash': trash_stats()})
            elif post and len(p) == 3 and p[0] == 'api' and p[1] in ('open', 'delete'):
                gid = int(p[2])
                with LOCK:
                    g = GROUPS.get(gid)
                if g is None:
                    raise Gone('пары уже нет — список обновлён')
                if p[1] == 'open':
                    if not g['v']:
                        raise LookupError('у этого превью нет видео')
                    open_file(g['v'][0][0], front=True)
                    self.reply(200, {'ok': True})
                else:
                    delete_group(gid)
                    self.reply(200, {'ok': True, 'trash': trash_stats()})
            else:
                self.reply(404, {'error': 'не найдено'})
        except ConnectionError:
            self.close_connection = True
        except Fail as e:
            self.reply(e.code, {'error': str(e)})
        except MoveError as e:
            code = 409 if isinstance(e.cause, PermissionError) else 500
            self.reply(code, {'error': explain(e), 'detail': str(e.cause),
                              'resync': isinstance(e.cause, FileNotFoundError)})
        except Gone as e:
            self.reply(404, {'error': str(e), 'resync': True})
        except (LookupError, ValueError) as e:
            self.reply(404, {'error': str(e)})
        except OSError as e:
            self.close_connection = True
            self.reply(500, {'error': str(e)})


class Server(ThreadingHTTPServer):
    daemon_threads = True
    # В Windows SO_REUSEADDR разрешает занять порт, который уже слушает другая программа (в том числе второй
    # экземпляр этой же): запросы окна попадали на чужой сервер с другим ключом и получали «нет доступа».
    # Поэтому в Windows порт занимается монопольно, а занятый порт даёт ошибку и берётся другой.
    allow_reuse_address = os.name != 'nt'

    def server_bind(self):
        if os.name == 'nt' and hasattr(socket, 'SO_EXCLUSIVEADDRUSE'):
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
        super().server_bind()

    def handle_error(self, request, client_address):
        if not isinstance(sys.exc_info()[1], ConnectionError):
            super().handle_error(request, client_address)


# ───────────────────────── своё окно (pywebview) ─────────────────────────

class WindowApi:
    """Методы, которые страница вызывает через window.pywebview.api (имена с подчёркиванием наружу не выдаются)."""

    def __init__(self):
        self._window = None
        self._fs = False

    def set_fullscreen(self, on):
        """Полный экран окна для крупного просмотра: в окне pywebview HTML-полноэкранный режим не годится."""
        on = bool(on)
        if self._window is not None and on != self._fs:
            self._window.toggle_fullscreen()
            self._fs = on
        return self._fs


def run_window(url, title, width=1600, height=1000):
    """Показать галерею в собственном окне. Блокирует, пока окно не закроют.

    True — окно было показано и закрыто; False — окно открыть не вышло (нет pywebview, нет WebView2, нет дисплея),
    тогда вызывающий откроет браузер.
    """
    try:
        import webview
    except ImportError:
        print('Для отдельного окна нужен pywebview: pip install pywebview (подробнее — в справке). Открываю в браузере.')
        return False
    api = WindowApi()
    try:
        win = webview.create_window(title, url, js_api=api, width=width, height=height, min_size=(900, 600),
                                    background_color='#2b2b2b', text_select=True)
        api._window = win
        WIN['window'] = win
        # на Windows принудительно WebView2: запасной движок IE страницу не потянет
        webview.start(gui='edgechromium' if os.name == 'nt' else None)
    except Exception as e:  # noqa: BLE001 — любой сбой окна не должен убивать программу: есть браузер
        print('Окно не открылось (%s: %s). Открываю в браузере.' % (type(e).__name__, e))
        return False
    return True


# ───────────────────────── страница ─────────────────────────

PAGE = r"""<!doctype html>
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Video Manager</title>
<style>
:root{color-scheme:dark;--bg:#2b2b2b;--cell:#363636;--well:#1e1e1e;--line:#474747;--text:#dcdcdc;--dim:#a0a0a0;--pick:#f2f2f2;--bad:#c9524e;--w:480px;--hh:52px}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font:14px/1.4 "Segoe UI Variable Text","Segoe UI",system-ui,sans-serif}
.dim{color:var(--dim)}
header{position:sticky;top:0;z-index:5;display:flex;flex-wrap:wrap;align-items:center;gap:8px 20px;padding:10px 16px;background:var(--bg);border-bottom:1px solid var(--line)}
#cnt{font-weight:600}
label{display:flex;align-items:center;gap:8px;color:var(--dim)}
button,select{font:inherit;color:var(--text);background:#3d3d3d;border:1px solid #5a5a5a;border-radius:5px;padding:5px 11px;cursor:pointer}
button:hover:not(:disabled){background:#484848}
button:disabled{opacity:.45;cursor:default}
.del:hover:not(:disabled){border-color:var(--bad);color:#f1b9b6}
:focus-visible{outline:2px solid var(--pick);outline-offset:2px}
input[type=range]{width:140px;accent-color:var(--pick)}
#keys{margin-left:auto;display:flex;flex-wrap:wrap;gap:6px 16px;font-size:12px;color:var(--dim)}
kbd{font:inherit;color:var(--text);padding:1px 6px;margin-right:4px;background:#383838;border:1px solid #555;border-bottom-width:2px;border-radius:4px}

#wrap{display:flex;align-items:flex-start}
main{flex:1;min-width:0}
#tree{flex:0 0 260px;position:sticky;top:var(--hh);max-height:calc(100vh - var(--hh));overflow:auto;padding:12px 10px 20px 12px;border-right:1px solid var(--line)}
body.notree #tree{display:none}
.deep{margin:0 0 10px;padding:0 8px}
button.dir{display:flex;width:100%;align-items:center;gap:8px;margin:1px 0;padding:5px 8px;text-align:left;background:none;border:0;border-radius:5px}
button.dir:hover:not(:disabled){background:#383838}
button.dir.on{background:#4a4a4a;font-weight:600}
button.dir.zero{color:var(--dim)}
button.dir.on.zero{font-weight:400}
.dn{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.dc{font-size:12px;color:var(--dim)}
#empty{margin:0;padding:28px 16px}

#grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(min(var(--w),100%),1fr));gap:14px;padding:16px}
figure{margin:0;background:var(--cell);border-radius:6px;overflow:hidden;scroll-margin:calc(var(--hh) + 8px) 0 24px}
figure.sel{outline:2px solid var(--pick);outline-offset:1px;background:#454545}
figure.wait{opacity:.55}
figure.bad,figure.bad.sel{outline:2px solid var(--bad);outline-offset:1px}
.err{padding:7px 10px;background:#3b2523;color:#f3c1bd;font-size:12px;line-height:1.35}
.im{position:relative;aspect-ratio:16/10;background:var(--well);cursor:zoom-in}
.im img{position:absolute;inset:0;width:100%;height:100%;object-fit:contain}
.nov{position:absolute;right:8px;top:8px;padding:2px 8px;border-radius:4px;background:var(--bad);color:#fff;font-size:12px;font-weight:600}
figcaption{padding:8px 10px 9px}
.nm{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:500}
.row{display:flex;align-items:center;gap:12px;min-height:30px;font-size:12px;color:var(--dim)}
.bt{display:none;gap:6px;margin-left:auto}
figure.sel .bt,figure:hover .bt{display:flex}
.bt button{padding:3px 9px;font-size:12px}

#v{position:fixed;inset:0;z-index:10;display:flex;flex-direction:column;background:var(--well)}
#v[hidden],#verr[hidden]{display:none}
#vi{flex:1;min-height:0;width:100%;object-fit:contain}
#vb{display:flex;flex-wrap:wrap;align-items:center;gap:8px 12px;padding:10px 16px;background:var(--bg);border-top:1px solid var(--line)}
body.nobar #vb{display:none}
#verr{position:absolute;left:0;right:0;top:0;z-index:2;padding:10px 16px;background:#7a2f2b;color:#fff;font-weight:600}
#v.wait #vi{opacity:.5}
body.wait,body.wait *{cursor:progress}
#vname{flex:1;min-width:120px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:600}
#vmeta{display:flex;gap:12px;color:var(--dim)}
#cut{position:relative;padding:12px 16px 8px;background:#242424;border-top:1px solid var(--line)}
#ctrack{position:relative;height:46px;border-radius:4px;background:#34503a;cursor:crosshair;touch-action:none;user-select:none}
.creg{position:absolute;top:0;bottom:0;background:#a3403acc;border-left:2px solid #f07a72;border-right:2px solid #f07a72;cursor:pointer}
.creg.on{box-shadow:0 0 0 2px #fff;z-index:1}
.creg i{position:absolute;top:0;bottom:0;right:0;background:repeating-linear-gradient(135deg,#34503a 0 5px,#5d7a63 5px 10px)}
#ccur,#cmark{position:absolute;top:-5px;bottom:-5px;width:2px;margin-left:-1px;pointer-events:none;z-index:2}
#ccur{background:#fff}
#cmark{background:#6ea8ff}
#cticks{position:relative;height:18px;margin-top:3px;font-size:11px;color:var(--dim)}
#cticks span{position:absolute;transform:translateX(-50%);white-space:nowrap}
#crow{display:flex;flex-wrap:wrap;align-items:center;gap:8px 10px;margin-top:4px}
#cinfo{flex:1;min-width:240px}
#chelp{margin:6px 0 0;font-size:12px}
#cpop{position:absolute;bottom:calc(100% - 6px);z-index:3;padding:4px;border:1px solid #5a5a5a;border-radius:6px;background:#111;box-shadow:0 8px 24px #000a;pointer-events:none}
#ctile{position:relative;width:320px;background:#000 no-repeat}
#cimg{position:absolute;left:4px;top:4px;width:320px;visibility:hidden}
#cimg.on{visibility:visible}
#ctime{display:block;padding-top:3px;text-align:center;font-size:12px;font-variant-numeric:tabular-nums}
#v.cutting #prev,#v.cutting #next,#v.cutting #pdir,#v.cutting #ndir,#v.cutting #vdel,#v.cutting #vcut{pointer-events:none;opacity:.4}
#toast{position:fixed;left:50%;bottom:24px;transform:translateX(-50%);z-index:20;max-width:90vw;padding:8px 14px;border-radius:6px;background:#202020;border:1px solid #5a5a5a;opacity:0;pointer-events:none}
body.viewing #toast{bottom:76px}
#toast.on{opacity:1}
#toast.bad{border-color:var(--bad)}
@media (prefers-reduced-motion:no-preference){#toast{transition:opacity .2s}}
@media (max-width:760px){
  #wrap{flex-direction:column;align-items:stretch}
  #tree{position:static;max-height:240px;flex-basis:auto;border-right:0;border-bottom:1px solid var(--line)}
}

[hidden]{display:none !important}
#tabs{display:flex}
.tab{background:#333;border:1px solid #5a5a5a;border-radius:0;padding:5px 14px}
.tab:first-child{border-radius:5px 0 0 5px}
.tab:last-child{border-radius:0 5px 5px 0;border-left:0}
.tab.on{background:#4d4d4d;border-color:#808080;font-weight:600}
.tab .n{margin-left:6px;color:var(--dim);font-weight:400}
button.go{background:#e8e8e8;border-color:#e8e8e8;color:#1c1c1c;font-weight:600}
button.go:hover:not(:disabled){background:#fff}
button.danger{border-color:var(--bad);color:#f3c1bd}
button.danger:hover:not(:disabled){background:#4a2a28}
body.mode-v .op{display:none !important}
input[type=checkbox]{accent-color:#e8e8e8}
body.mode-v #grid,body.mode-v #empty{display:none}
#vl{display:none;padding:0 16px 28px}
body.mode-v #vl{display:block}
#vtool{position:sticky;top:var(--hh);z-index:4;display:flex;flex-wrap:wrap;align-items:center;gap:8px 12px;padding:12px 0;background:var(--bg);border-bottom:1px solid var(--line)}
#vsel{margin-right:auto;font-weight:600}
#vign,#vfmt{margin:10px 0 0;font-size:12px}
#fact{display:flex;flex-direction:column;gap:6px;margin:0 0 12px;padding:0 4px}
#fact button{width:100%;text-align:left}
#dlg{position:fixed;inset:0;z-index:40;display:flex;align-items:center;justify-content:center;background:#000a}
#dlg .box{width:min(540px,calc(100vw - 32px));padding:18px;border:1px solid #5a5a5a;border-radius:10px;background:#252525;box-shadow:0 12px 40px #000a}
#dtxt{margin:0 0 16px;line-height:1.55;white-space:pre-line;max-height:60vh;overflow:auto}
#dlg .acts{display:flex;justify-content:flex-end;gap:8px}
.pk{position:absolute;left:8px;top:8px;z-index:2;width:24px;height:24px;border:2px solid #e8e8e8;border-radius:6px;background:#000a;opacity:0;cursor:pointer}
figure:hover .pk,body.picking .pk{opacity:1}
figure.pick{box-shadow:0 0 0 3px #6ea8ff}
figure.pick .pk{opacity:1;border-color:#6ea8ff;background:#6ea8ff}
figure.pick .pk::after{content:'✓';position:absolute;inset:0;display:flex;align-items:center;justify-content:center;color:#10243f;font-size:16px;font-weight:700}
#selbar{flex-basis:100%;display:flex;flex-wrap:wrap;align-items:center;gap:8px 10px}
#selcnt{margin-right:6px;font-weight:600;color:#9cc4ff}
#vi{cursor:zoom-out}
#fact2{display:flex;gap:6px;margin:0 0 12px;padding:0 4px}
#fact2 button{flex:1;min-width:0}
#jobbar{flex-basis:100%;margin-top:-2px}
.jrow{display:flex;align-items:center;gap:12px;color:var(--dim);font-size:13px}
.jrow span{flex:1;min-width:0}
.jrow button{padding:2px 10px;font-size:12px}
#vnote{margin:12px 0 0;padding:10px 12px;border-radius:6px;background:#3a3326;color:#f1ddaa;line-height:1.5}
code{padding:1px 6px;border-radius:4px;background:#00000040;font-family:Consolas,"Cascadia Mono",monospace;font-size:13px}
#vprog{margin:12px 0 0;color:var(--dim);font-size:13px}
.bar{height:6px;margin-bottom:4px;border-radius:3px;background:#444;overflow:hidden}
.bar i{display:block;width:0;height:100%;background:var(--pick)}
.grp{margin-top:16px}
.gh{display:flex;align-items:center;gap:10px;padding:7px 8px;border-radius:6px;background:var(--cell);color:var(--text);font-weight:600;cursor:pointer}
.gh .gc{font-size:12px;font-weight:400;color:var(--dim)}
.gh .tag{margin-left:auto;font-size:12px;font-weight:400;color:var(--dim)}
.vr{display:flex;flex-wrap:wrap;align-items:center;gap:4px 12px;padding:5px 8px 5px 26px;border-bottom:1px solid #353535}
.vr label{flex:1;min-width:0;gap:10px;color:var(--text);cursor:pointer}
.vn{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.vs,.vd{font-size:12px;color:var(--dim);white-space:nowrap}
.vr button{padding:2px 9px;font-size:12px}
.vr.bad{background:#35201f}
.verr{flex-basis:100%;padding-left:26px;color:#f3c1bd;font-size:12px}
.pad{padding:20px 8px}
#trashp,#rootp{position:fixed;right:16px;top:calc(var(--hh) + 6px);z-index:30;width:min(400px,calc(100vw - 32px));padding:14px;border:1px solid #5a5a5a;border-radius:8px;background:#202020;box-shadow:0 8px 28px #0008}
#trashp p,#rootp p{margin:0;line-height:1.5}
#trashp .acts,#rootp .acts{display:flex;flex-wrap:wrap;gap:8px;margin-top:12px}
#rootp{left:16px;right:auto;width:min(520px,calc(100vw - 32px))}
#rooti{word-break:break-all}
#rootl{display:flex;flex-direction:column;gap:4px;margin-top:10px;max-height:50vh;overflow:auto}
#rootl button{display:flex;flex-direction:column;align-items:flex-start;text-align:left;padding:5px 10px}
#rootl .dim{font-size:12px;word-break:break-all}
#rootb{max-width:260px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:600}
</style>
</head>
<body>
<header>
  <button id="rootb" title="Открыть другую папку"></button>
  <div id="tabs">
    <button id="tab-p" class="tab on">Превью <span id="np" class="n"></span></button>
    <button id="tab-v" class="tab">Видео без превью <span id="nv" class="n"></span></button>
  </div>
  <span id="cnt"></span>
  <button id="refresh" title="Перечитать папку: найти новые видео и превью, убрать пропавшие (F5)">Обновить</button>
  <label class="op">Порядок
    <select id="srt">
      <option value="name">по имени</option>
      <option value="new">новые сверху</option>
      <option value="old">старые сверху</option>
      <option value="big">крупные сверху</option>
    </select>
  </label>
  <label class="op">Размер превью <input id="sz" type="range" min="200" max="1600" step="20"></label>
  <button id="und" class="op" disabled>Отменить удаление</button>
  <button id="trash" hidden title="Файлы, которые вы удалили в галерее и которые ещё лежат в папке _на_удаление"></button>
  <button id="tg" title="Показать или скрыть дерево папок">Папки</button>
  <button id="redo" class="op" hidden title="Заменить превью в этой папке новыми: сетка, размер и вид задаются параметрами запуска. Старые превью уйдут в _на_удаление"></button>
  <button id="orph" class="op" hidden title="Превью, у которых нет видео (на плитке отмечены «нет видео»), будут перенесены в _на_удаление. Ctrl+Z вернёт их"></button>
  <div id="selbar" class="op" hidden>
    <span id="selcnt"></span>
    <button id="sdel" class="danger" title="Перенести выбранные пары в _на_удаление (Del). Ctrl+Z вернёт все сразу"></button>
    <button id="sredo" title="Заменить превью выбранных новыми"></button>
    <button id="splay" title="Запустить выбранные видео в MPC"></button>
    <button id="sall" title="Выделить все превью в этом списке (Ctrl+A)">Выбрать все</button>
    <button id="snone" title="Снять выделение (Esc)">Снять выделение</button>
  </div>
  <div id="jobbar" hidden>
    <div class="bar"><i id="vbar"></i></div>
    <div class="jrow"><span id="vptxt"></span><button id="vstop" hidden>Остановить</button></div>
  </div>
  <span id="keys" class="op">
    <span><kbd>Стрелки</kbd>выбор</span>
    <span><kbd>Пробел</kbd>на весь экран</span>
    <span><kbd>Enter</kbd>открыть видео</span>
    <span><kbd>E</kbd>в проводнике</span>
    <span><kbd>Del</kbd>удалить пару</span>
    <span><kbd>PgUp PgDn</kbd>папки</span>
    <span><kbd>X</kbd>выделить</span>
    <span><kbd>Ctrl+Z</kbd>отменить</span>
  </span>
</header>
<div id="rootp" hidden>
  <p>Открыта папка: <span id="rooti" class="dim"></span></p>
  <div id="rootl"></div>
  <div class="acts">
    <button id="rpick" class="go">Выбрать другую папку…</button>
    <button id="rcancel">Отмена</button>
  </div>
</div>
<div id="trashp" hidden>
  <p id="trashi"></p>
  <div class="acts">
    <button id="tpurge" class="danger">Удалить насовсем</button>
    <button id="topen">Открыть папку</button>
    <button id="tcancel">Отмена</button>
  </div>
</div>
<div id="wrap">
  <aside id="tree">
    <label class="deep"><input type="checkbox" id="deep"> включая подпапки</label>
    <div id="fact">
      <button id="fexp" title="Открыть выбранную папку в проводнике">Открыть в проводнике</button>
      <button id="fplay">Воспроизвести в MPC</button>
      <button id="fmpc">Добавить в плейлист MPC</button>
    </div>
    <div id="fact2">
      <button id="fdel" class="danger" title="Перенести выбранную папку целиком (с подпапками и любыми файлами) в _на_удаление">Удалить папку…</button>
      <button id="fempty" title="Найти папки без файлов и перенести их в _на_удаление">Пустые папки…</button>
    </div>
    <nav id="dirs"></nav>
  </aside>
  <main>
    <div id="grid"></div>
    <p id="empty" class="dim" hidden></p>
    <section id="vl">
      <div id="vtool">
        <span id="vsel"></span>
        <button id="vall" title="Отметить все видео в этом списке, кроме папок, помеченных «не создавать»">Выбрать все</button>
        <button id="vnone">Снять все</button>
        <button id="vmake" class="go">Создать превью</button>
      </div>
      <div id="vnote" hidden></div>
      <p id="vfmt" class="dim"></p>
      <p id="vign" class="dim" hidden></p>
      <div id="vrows"></div>
    </section>
  </main>
</div>
<div id="v" hidden>
  <div id="verr" hidden></div>
  <img id="vi" alt="">
  <div id="cut" hidden>
    <div id="cpop" hidden><div id="ctile"></div><img id="cimg" alt=""><span id="ctime"></span></div>
    <div id="ctrack"><div id="cregs"></div><div id="cmark" hidden></div><div id="ccur"></div></div>
    <div id="cticks"></div>
    <div id="crow">
      <span id="cinfo"></span>
      <button id="chead" title="Вырезать всё от начала видео до курсора">Отрезать начало</button>
      <button id="ctail" title="Вырезать всё от курсора до конца видео">Отрезать конец</button>
      <button id="cin" title="Начало вырезаемого куска — там, где курсор (I)">Начало куска (I)</button>
      <button id="cout" title="Конец вырезаемого куска — там, где курсор (O)">Конец куска (O)</button>
      <button id="cdel" title="Убрать выбранный кусок из вырезаемых (Del)">Не вырезать кусок</button>
      <button id="cclr">Сбросить</button>
      <button id="cgo" class="go">Обрезать…</button>
      <button id="cstop" hidden>Остановить</button>
      <button id="cexit" title="Закрыть обрезку (Esc)">Закрыть</button>
    </div>
    <p id="chelp" class="dim">Протяните мышью по шкале — этот кусок будет вырезан; края кусков можно двигать. Клик — курсор.
      ←/→ — курсор на 1 с, с Shift — на 10 с, с Ctrl — на минуту. Красное вырезается; полосатое останется:
      без перекодирования оставшийся кусок начинается с ключевого кадра.</p>
  </div>
  <div id="vb">
    <button id="prev" title="Назад (←)">‹</button>
    <button id="next" title="Вперёд (→)">›</button>
    <span id="vname"></span>
    <span id="vpos" class="dim"></span>
    <span id="vmeta"></span>
    <button id="pdir" title="Предыдущая папка ([)">Пред. папка</button>
    <button id="ndir" title="Следующая папка (])">След. папка</button>
    <button id="vpk" title="Выбрать для групповых действий (X)">Выбрать (X)</button>
    <button id="vopen" title="Открыть видео (Enter)">Открыть видео</button>
    <button id="vcut" title="Вырезать лишнее из видео: начало, конец или куски из середины (C)">Обрезать видео</button>
    <button id="vdel" class="del" title="Удалить пару (Del)">Удалить пару</button>
    <button id="vclose" title="Выйти (Esc). Клавиша I скрывает эту панель">Закрыть</button>
  </div>
</div>
<div id="dlg" hidden>
  <div class="box">
    <p id="dtxt"></p>
    <div class="acts"><button id="dno">Отмена</button><button id="dok" class="go">Продолжить</button></div>
  </div>
</div>
<div id="toast"></div>
<script>
const T = new URLSearchParams(location.search).get('t');
const q = p => p + (p.includes('?') ? '&' : '?') + 't=' + encodeURIComponent(T);
const $ = s => document.querySelector(s);
const grid = $('#grid');
const SETTINGS = /*SETTINGS*/{};
let saveTimer = 0;
const saveNow = () => {
  clearTimeout(saveTimer);
  saveTimer = 0;
  return fetch(q('/api/settings'), {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(SETTINGS)}).catch(() => {});
};
const store = {
  get: k => (k in SETTINGS ? SETTINGS[k] : null),
  set: (k, v) => {
    SETTINGS[k] = String(v);
    clearTimeout(saveTimer);
    saveTimer = setTimeout(saveNow, 400);
  },
  // перед сменой папки: отложенная запись ушла бы уже в настройки новой папки
  flush: () => (saveTimer ? saveNow() : Promise.resolve()),
};
let all = [], items = [], videos = [], cur = 0, viewer = false, undoN = 0, busy = false;
let mode = 'previews', inited = false;
let folder = '', ROOT = '', ROOT_PATH = '', recent = [];
let sel = new Map();                 // ручные отметки видео: id → true/false
let skipDirs = new Set();            // папки, где превью создавать не нужно (запоминаются)
let skipLoaded = false;
let job = {running: false, total: 0, done: 0, ok: 0, failed: {}, active: [], elapsed: 0};
let ff = {ok: true, drawtext: true};
let trashInfo = {files: 0, bytes: 0};
let jobTimer = 0, wasRunning = false, lastFail = 0;
let ign = {exts: [], files: 0};
let mpc = {ok: false, name: ''};
let picked = new Set(), anchor = -1;   // выделенные плитки (номера пар) и опорная плитка для Shift+клик
let opts = {cols: 10, rows: 9, width: 2560, header: false, hw: ''};
let refreshing = false;
let C = null;                        // открытая обрезка видео (см. «обрезка видео»)
const purl = it => q('/p/' + it.id + '?v=' + Math.round(it.pm || 0));
let sort = store.get('srt') || 'name';
let deep = store.get('deep') !== '0';
let treeOn = store.get('tree') !== '0';
const knownDirs = new Set(['']);

const esc = s => s.replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
const full = it => it.dir ? it.dir + '/' + it.name : it.name;
const segCmp = (a, b) => {
  const x = a.split('/'), y = b.split('/');
  for (let i = 0; i < Math.min(x.length, y.length); i++) {
    const c = x[i].localeCompare(y[i], undefined, {numeric: true, sensitivity: 'base'});
    if (c) return c;
  }
  return x.length - y.length;
};
const byName = (a, b) => segCmp(a.dir, b.dir) ||
  a.name.localeCompare(b.name, undefined, {numeric: true, sensitivity: 'base'});
const SORTS = {
  name: byName,
  new: (a, b) => b.mtime - a.mtime || byName(a, b),
  old: (a, b) => a.mtime - b.mtime || byName(a, b),
  big: (a, b) => b.size - a.size || byName(a, b),
};
const inView = it => deep
  ? (folder === '' || it.dir === folder || it.dir.startsWith(folder + '/'))
  : it.dir === folder;
const label = it => {
  const rel = !folder ? it.dir : it.dir === folder ? '' : it.dir.slice(folder.length + 1);
  return rel ? rel + '/' + it.name : it.name;
};

const fmtSize = n => n >= 2 ** 30 ? (n / 2 ** 30).toFixed(2).replace('.', ',') + ' ГБ'
  : n >= 2 ** 20 ? Math.round(n / 2 ** 20) + ' МБ' : Math.max(1, Math.round(n / 1024)) + ' КБ';
const fmtDate = t => new Date(t * 1000).toLocaleDateString('ru-RU');
const plural = (n, f) => f[n % 10 === 1 && n % 100 !== 11 ? 0 : n % 10 >= 2 && n % 10 <= 4 && (n % 100 < 10 || n % 100 >= 20) ? 1 : 2];
const fmtEta = s => s < 90 ? Math.max(5, Math.round(s)) + ' с' : s < 5400 ? Math.round(s / 60) + ' мин'
  : Math.floor(s / 3600) + ' ч ' + Math.round(s % 3600 / 60) + ' мин';

function parts(it) {
  if (!it.nv) return [];
  const r = [fmtSize(it.size), fmtDate(it.mtime)];
  if (it.nv > 1) r.push('видео: ' + it.nv);
  return r;
}
const spans = it => parts(it).map(s => '<span>' + s + '</span>').join('');

function toast(msg, bad) {
  const t = $('#toast');
  t.textContent = msg;
  t.className = 'on' + (bad ? ' bad' : '');
  clearTimeout(toast.h);
  toast.h = setTimeout(() => { t.className = ''; }, bad ? 9000 : 2600);
}

async function api(path, post, body) {
  const opt = post ? {method: 'POST'} : {};
  if (body !== undefined) {
    opt.headers = {'Content-Type': 'application/json'};
    opt.body = JSON.stringify(body);
  }
  const r = await fetch(q(path), opt);
  const j = await r.json().catch(() => ({}));
  if (!r.ok) {
    const err = new Error(j.error || 'ошибка ' + r.status);
    err.resync = !!j.resync;
    throw err;
  }
  return j;
}

/* ───── дерево папок ───── */

function dirList() {
  const s = new Set(['']);
  knownDirs.forEach(d => {
    const p = d.split('/');
    for (let i = 1; i <= p.length; i++) s.add(p.slice(0, i).join('/'));
  });
  return [...s].sort((a, b) => a === '' ? -1 : b === '' ? 1 : segCmp(a, b));
}
const src = () => mode === 'videos' ? videos : all;
function counts() {
  const direct = {}, agg = {};
  for (const it of src()) {
    direct[it.dir] = (direct[it.dir] || 0) + 1;
    agg[''] = (agg[''] || 0) + 1;
    const p = it.dir ? it.dir.split('/') : [];
    for (let i = 1; i <= p.length; i++) {
      const k = p.slice(0, i).join('/');
      agg[k] = (agg[k] || 0) + 1;
    }
  }
  return {direct, agg};
}
const countIn = (C, d) => (deep ? C.agg[d] : C.direct[d]) || 0;

function renderTree() {
  const list = dirList(), C = counts();
  folderStat();
  document.body.classList.toggle('notree', !treeOn);
  $('#dirs').innerHTML = list.map(d => {
    const depth = d ? d.split('/').length : 0;
    const n = countIn(C, d);
    return '<button class="dir' + (d === folder ? ' on' : '') + (n ? '' : ' zero') + '" data-d="' + esc(d) +
      '" title="' + esc(d || ROOT) + '" style="padding-left:' + (8 + depth * 14) + 'px">' +
      '<span class="dn">' + esc(d ? d.split('/').pop() : ROOT) + '</span><span class="dc">' + n + '</span></button>';
  }).join('');
}

function setFolder(d) {
  folder = d;
  if (mode === 'videos') { renderVideos(); renderTree(); return; }
  applyView(null);
  select(0);
}

// ближайшая за пределами текущего списка папка, где напрямую лежат превью (undefined — такой нет)
function neighbor(dir) {
  const list = dirList(), C = counts();
  const L = list.filter(d => (C.direct[d] || 0) > 0);
  const inV = d => deep ? (folder === '' || d === folder || d.startsWith(folder + '/')) : d === folder;
  const idx = [];
  L.forEach((d, i) => { if (inV(d)) idx.push(i); });
  if (idx.length) return L[dir > 0 ? idx[idx.length - 1] + 1 : idx[0] - 1];
  // текущий список пуст — ориентируемся по месту папки в дереве
  const at = list.indexOf(folder);
  const after = L.filter(d => list.indexOf(d) > at), before = L.filter(d => list.indexOf(d) < at);
  return dir > 0 ? after[0] : before[before.length - 1];
}

// перейти в соседнюю папку; last — встать на её последнее превью, иначе на первое
function crossFolder(dir, last, quiet) {
  const t = neighbor(dir);
  if (t === undefined) {
    if (!quiet) {
      const multi = new Set(items.map(i => i.dir)).size > 1;
      toast(multi ? 'Показано сразу несколько папок: выберите одну слева'
        : dir > 0 ? 'Дальше папок с превью нет' : 'Раньше папок с превью нет');
    }
    return false;
  }
  folder = t;
  applyView(null);
  let k = -1;
  items.forEach((it, i) => { if (it.dir === t && (last || k < 0)) k = i; });
  select(k < 0 ? 0 : k);
  toast('Папка: ' + (t || ROOT));
  return true;
}

/* ───── сетка ───── */

function tile(it) {
  const f = document.createElement('figure');
  f.dataset.id = it.id;
  if (it.err) f.classList.add('bad');
  if (picked.has(it.id)) f.classList.add('pick');
  f.innerHTML =
    '<div class="im"><span class="pk" title="Выделить: клик здесь, X или Ctrl+клик по превью; Shift+клик — диапазон"></span><img loading="lazy" alt="" src="' + purl(it) + '">' +
    (it.nv ? '' : '<b class="nov">нет видео</b>') + '</div>' +
    '<figcaption>' + (it.err ? '<div class="err">' + esc(it.err) + '</div>' : '') +
    '<div class="nm" title="' + esc(full(it)) + '">' + esc(label(it)) + '</div>' +
    '<div class="row">' + spans(it) +
    '<span class="bt"><button data-a="open"' + (it.nv ? '' : ' disabled') + '>Открыть видео</button>' +
    '<button data-a="del" class="del">Удалить пару</button></span></div></figcaption>';
  return f;
}

function stat() {
  $('#np').textContent = all.length;
  $('#nv').textContent = videos.length;
  if (mode === 'previews') {
    $('#cnt').textContent = items.length + ' превью' + (items.length !== all.length ? ' из ' + all.length : '');
  }
  $('#und').textContent = 'Отменить удаление' + (undoN ? ' (' + undoN + ')' : '');
  $('#und').disabled = !undoN;
  redoStat();
  $('#empty').hidden = items.length > 0;
  $('#empty').textContent = all.length
    ? 'В этой папке превью нет. Клавиши [ и ] переключают папки.'
    : videos.length ? 'Превью пока нет. Создайте их во вкладке «Видео без превью».' : 'Превью не осталось.';
}

function render() {
  const frag = document.createDocumentFragment();
  items.forEach(it => frag.append(tile(it)));
  grid.innerHTML = '';
  grid.append(frag);
  stat();
  renderTree();
  select(cur, false);
  pickStat();
}

// focusId: undefined — остаться на текущем превью, null — начать сначала, число — встать на это превью
function applyView(focusId) {
  if (focusId === undefined && items[cur]) focusId = items[cur].id;
  items = all.filter(inView).sort(SORTS[sort]);
  const vis = new Set(items.map(i => i.id));
  picked.forEach(id => { if (!vis.has(id)) picked.delete(id); });   // выделенным остаётся только то, что сейчас в списке
  cur = focusId == null ? 0 : Math.max(0, items.findIndex(x => x.id === focusId));
  render();
}

function select(i, scroll = true) {
  if (!items.length) { if (viewer) closeViewer(); return; }
  cur = Math.max(0, Math.min(items.length - 1, i));
  const old = grid.querySelector('.sel');
  if (old) old.classList.remove('sel');
  const f = grid.children[cur];
  f.classList.add('sel');
  if (scroll) f.scrollIntoView({block: 'nearest'});
  if (viewer) showViewer();
}

function go(n) {
  if (viewer && (n < 0 || n >= items.length)) {
    const fwd = n >= items.length;
    if (!crossFolder(fwd ? 1 : -1, !fwd, true)) toast(fwd ? 'Это последнее превью' : 'Это первое превью');
    return;
  }
  select(n);
}

/* ───── крупный просмотр (на весь экран) ───── */

function showViewer() {
  if (C && (!viewer || !items[cur] || items[cur].id !== C.id)) closeCut(true);
  $('#v').hidden = !viewer;
  document.body.classList.toggle('viewing', viewer);
  if (!viewer) return;
  const it = items[cur];
  $('#vi').src = purl(it);
  $('#vname').textContent = full(it);
  $('#vname').title = full(it);
  $('#vpk').textContent = picked.has(it.id) ? '✓ Выбрано' : 'Выбрать (X)';
  $('#vpos').textContent = (cur + 1) + ' из ' + items.length;
  $('#vmeta').innerHTML = spans(it);
  $('#vopen').disabled = !it.nv;
  $('#vcut').disabled = it.nv !== 1;
  $('#verr').hidden = !it.err;
  $('#verr').textContent = it.err ? 'Не удалено: ' + it.err : '';
  for (const d of [1, 2, -1]) if (items[cur + d]) new Image().src = purl(items[cur + d]);
}

const winApi = () => (window.pywebview && window.pywebview.api && window.pywebview.api.set_fullscreen) ? window.pywebview.api : null;
function enterFs() {
  if (winApi()) { winApi().set_fullscreen(true); return; }
  const el = document.documentElement;
  if (!document.fullscreenElement && el.requestFullscreen) {
    const p = el.requestFullscreen();
    if (p && p.catch) p.catch(() => {});
  }
}
function leaveFs() {
  if (winApi()) { winApi().set_fullscreen(false); return; }
  if (document.fullscreenElement && document.exitFullscreen) {
    const p = document.exitFullscreen();
    if (p && p.catch) p.catch(() => {});
  }
}
function openViewer() {
  if (!items.length) return;
  viewer = true;
  showViewer();
  enterFs();
}
function closeViewer(exitFs = true) {
  viewer = false;
  showViewer();
  if (exitFs) leaveFs();
}
// Esc в полноэкранном режиме обрабатывает сам браузер — просмотр закрываем по выходу из полного экрана
document.addEventListener('fullscreenchange', () => { if (!document.fullscreenElement && viewer) closeViewer(false); });

/* ───── обрезка видео (без перекодирования) ───── */

// C — открытая обрезка: {id, d — длительность, info — сетка листа, cuts — вырезаемые куски [{a, b}], sel — выбранный кусок,
// cur — курсор, mark — начало куска (I), snaps — начало следующего оставляемого куска (ключевой кадр) по концу куска,
// L — где кадры в листе превью (null — лист не узнан, тогда только точные кадры), drag, running, status}
let cutTimer = 0, frameTimer = 0, frameBusy = false, frameWant = null;
const track = $('#ctrack');

const fmtT = (t, fine) => {
  const s = Math.max(0, t), h = Math.floor(s / 3600), m = Math.floor(s % 3600 / 60), x = s % 60;
  const ss = fine ? x.toFixed(1).padStart(4, '0') : String(Math.floor(x)).padStart(2, '0');
  return (h ? h + ':' + String(m).padStart(2, '0') : m) + ':' + ss;
};
const tpos = t => (100 * t / C.d) + '%';
const tAt = e => {
  const r = track.getBoundingClientRect();
  return Math.max(0, Math.min(C.d, (e.clientX - r.left) / r.width * C.d));
};
const pxT = px => px / Math.max(1, track.clientWidth) * C.d;
const snapEnds = t => (t < pxT(8) ? 0 : t > C.d - pxT(8) ? C.d : t);
// реальное начало оставляемого куска после вырезаемого: ключевой кадр не позже его конца (пока не известен — сам конец)
const keepStart = c => (c.b >= C.d - 0.05 ? C.d : (C.snaps[c.b.toFixed(2)] ?? c.b));
const removedOf = c => Math.max(0, Math.max(c.a, keepStart(c)) - c.a);

async function openCut() {
  const it = items[cur];
  if (!viewer || !it || C) return;
  if (!it.nv) { toast('У этого превью нет видео', true); return; }
  if (it.nv > 1) { toast('У пары несколько видеофайлов: непонятно, какой обрезать', true); return; }
  if (!ff.ok) { toast('ffmpeg не найден: обрезать нечем', true); return; }
  if (job.running) { toast('Идёт создание превью: обрезать можно после него', true); return; }
  let info;
  try {
    info = await api('/api/cut/info', true, {id: it.id});
  } catch (e) {
    toast('Обрезка недоступна: ' + e.message, true);
    return;
  }
  if (!viewer || items[cur] !== it) return;
  C = {id: it.id, d: info.duration, info, cuts: [], sel: -1, cur: 0, mark: null, snaps: {}, L: null,
       drag: null, running: false, status: null, popT: null};
  $('#v').classList.add('cutting');
  $('#cut').hidden = false;
  cutLayout();
  renderTicks();
  renderCut();
}

async function closeCut(force) {
  if (!C) return;
  if (!force && !C.running && C.cuts.length && !await ask('Закрыть обрезку? Отмеченные куски не сохранятся.', 'Закрыть')) return;
  if (C && C.running) toast('Обрезка продолжается: когда закончится, превью пересоздастся');
  C = null;
  hidePop();
  $('#cut').hidden = true;
  $('#v').classList.remove('cutting');
}

// где в листе превью лежит каждый кадр: сетка — от сервера (как её строит make_preview), размер листа — по картинке.
// Не сошлось (лист сделан не этой программой или с другими параметрами) — всплывают только точные кадры.
function cutLayout() {
  const im = $('#vi'), i = C.info, W = im.naturalWidth, H = im.naturalHeight;
  C.L = null;
  if (!W || W !== i.width || !i.w || !i.h) return;
  const tw = Math.floor((i.width - (i.cols - 1)) / i.cols);
  const th = (H - i.hh - (i.rows - 1)) / i.rows;
  if (!Number.isInteger(th) || Math.abs(th - tw * i.h / i.w) > 2.5) return;
  C.L = {tw, th, W, H, n: i.cols * i.rows};
}
$('#vi').addEventListener('load', () => { if (C) cutLayout(); });

function renderTicks() {
  const steps = [1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 900, 1800, 3600, 7200];
  const step = steps.find(x => C.d / x <= 10) || 7200;
  let h = '';
  for (let t = 0; t <= C.d + 0.001; t += step) h += '<span style="left:' + tpos(t) + '">' + fmtT(t) + '</span>';
  $('#cticks').innerHTML = h;
}

function normCuts() {
  let selObj = C.cuts[C.sel];
  C.cuts.forEach(c => { if (c.a > c.b) [c.a, c.b] = [c.b, c.a]; });
  const out = [];
  for (const c of C.cuts.filter(c => c.b - c.a >= 0.2).sort((x, y) => x.a - y.a)) {
    const p = out[out.length - 1];
    if (p && c.a <= p.b + 0.05) {
      p.b = Math.max(p.b, c.b);
      if (c === selObj) selObj = p;
    } else {
      out.push(c);
    }
  }
  C.cuts = out;
  C.sel = out.indexOf(selObj);
}

function needSnaps() {
  for (const c of C.cuts) {
    const k = c.b.toFixed(2);
    if (c.b >= C.d - 0.05 || k in C.snaps) continue;
    C.snaps[k] = null;  // запрошено
    const id = C.id;
    api('/api/cut/key', true, {id, at: +k})
      .then(r => { if (C && C.id === id) { C.snaps[k] = r.t; renderCut(); } })
      .catch(() => { if (C && C.id === id) delete C.snaps[k]; });
  }
}

function renderCut() {
  if (!C) return;
  $('#cregs').innerHTML = C.cuts.map((c, i) => {
    const left = c.b - Math.max(c.a, keepStart(c));  // эта часть останется: следующий кусок начнётся с ключевого кадра
    const hatch = left > 0.01 ? '<i style="width:' + (100 * left / (c.b - c.a)) + '%"></i>' : '';
    return '<div class="creg' + (i === C.sel ? ' on' : '') + '" data-i="' + i + '" style="left:' + tpos(c.a) +
      ';width:' + tpos(c.b - c.a) + '" title="' + fmtT(c.a, true) + ' – ' + fmtT(c.b, true) +
      (left > 0.01 ? ' (останется ' + left.toFixed(1) + ' с до ключевого кадра)' : '') + '">' + hatch + '</div>';
  }).join('');
  $('#ccur').style.left = tpos(C.cur);
  $('#cmark').hidden = C.mark === null;
  if (C.mark !== null) $('#cmark').style.left = tpos(C.mark);
  const n = C.cuts.length, kept = C.d - C.cuts.reduce((s, c) => s + removedOf(c), 0);
  let t;
  if (C.running) {
    const st = C.status || {};
    t = 'Обрезка: ' + (st.stage || 'подготовка') + (st.stage === 'обрезка' ? ' ' + (st.pct || 0) + '%' : '') + '…';
  } else {
    t = 'Курсор <b>' + fmtT(C.cur, true) + '</b> · ' + (n
      ? 'вырезается ' + n + ' ' + plural(n, ['кусок', 'куска', 'кусков']) + ', останется <b>' + fmtT(kept) + '</b> из ' + fmtT(C.d)
      : 'длительность ' + fmtT(C.d) + ' — отметьте, что вырезать');
    if (C.mark !== null) t += ' · начало куска: ' + fmtT(C.mark, true) + ', поставьте конец (O)';
  }
  $('#cinfo').innerHTML = t;
  for (const b of ['#chead', '#ctail', '#cin', '#cout', '#cclr']) $(b).disabled = C.running;
  $('#cdel').disabled = C.running || C.sel < 0;
  $('#cgo').hidden = C.running;
  $('#cgo').disabled = !n;
  $('#cstop').hidden = !C.running;
  if (!C.drag) needSnaps();
}

function addCut(a, b) {
  if (b - a < 0.2) { toast('Слишком короткий кусок'); return; }
  const c = {a, b};
  C.cuts.push(c);
  C.sel = C.cuts.length - 1;
  normCuts();
  renderCut();
}
function moveCur(t) {
  C.cur = Math.max(0, Math.min(C.d, t));
  renderCut();
  const r = track.getBoundingClientRect();
  popAt(C.cur, r.left + r.width * C.cur / C.d);
}
function cutOut() {
  if (C.mark === null) { toast('Сначала поставьте начало куска: клавиша I'); return; }
  const a = Math.min(C.mark, C.cur), b = Math.max(C.mark, C.cur);
  C.mark = null;
  addCut(a, b);
}
function delCut() {
  if (C.sel < 0) return;
  C.cuts.splice(C.sel, 1);
  C.sel = -1;
  renderCut();
}

/* всплывающий кадр над шкалой: сразу — клетка из листа превью, через миг — точный кадр от ffmpeg */
function popAt(t, clientX) {
  const pop = $('#cpop'), box = $('#cut').getBoundingClientRect(), i = C.info, PW = 320, tile = $('#ctile');
  C.popT = t;
  pop.hidden = false;
  if (C.L) {
    const L = C.L, k = Math.min(L.n - 1, Math.max(0, Math.round(t / C.d * L.n)));
    const col = k % i.cols, row = Math.floor(k / i.cols), s = PW / L.tw;
    tile.style.backgroundImage = 'url("' + $('#vi').src + '")';
    tile.style.backgroundSize = (L.W * s) + 'px ' + (L.H * s) + 'px';
    tile.style.backgroundPosition = (-col * (L.tw + 1) * s) + 'px ' + (-(i.hh + row * (L.th + 1)) * s) + 'px';
    tile.style.height = Math.round(L.th * s) + 'px';
  } else {
    tile.style.backgroundImage = 'none';
    tile.style.height = Math.round(PW * (i.h / i.w || 0.5625)) + 'px';
  }
  $('#ctime').textContent = fmtT(t, true);
  pop.style.left = Math.max(0, Math.min(box.width - PW - 12, clientX - box.left - PW / 2 - 4)) + 'px';
  const im = $('#cimg');
  if (im.dataset.t !== t.toFixed(1)) im.classList.remove('on');
  clearTimeout(frameTimer);
  frameTimer = setTimeout(() => { frameWant = t; frameNext(); }, 200);
}
function frameNext() {
  if (frameBusy || frameWant === null || !C) return;
  const t = frameWant, id = C.id, pre = new Image();
  frameWant = null;
  frameBusy = true;
  pre.onload = () => {
    frameBusy = false;
    if (C && C.id === id && C.popT !== null && Math.abs(C.popT - t) < 0.05) {
      const im = $('#cimg');
      im.src = pre.src;
      im.dataset.t = t.toFixed(1);
      im.classList.add('on');
    }
    frameNext();
  };
  pre.onerror = () => { frameBusy = false; frameNext(); };
  pre.src = q('/api/cut/frame/' + id + '?at=' + t.toFixed(2) + '&w=480');
}
function hidePop() {
  clearTimeout(frameTimer);
  frameWant = null;
  $('#cpop').hidden = true;
  $('#cimg').classList.remove('on');
  if (C) C.popT = null;
}

function edgeAt(e) {
  const t = tAt(e), tol = pxT(6);
  for (let i = 0; i < C.cuts.length; i++) {
    const c = C.cuts[i];
    if (Math.abs(t - c.a) <= tol) return {i, side: 'a'};
    if (Math.abs(t - c.b) <= tol) return {i, side: 'b'};
  }
  return null;
}
track.onpointerdown = e => {
  if (!C || C.running || e.button !== 0) return;
  try { track.setPointerCapture(e.pointerId); } catch (_) { /* без захвата: перетаскивание за край шкалы оборвётся */ }
  const t = tAt(e), ed = edgeAt(e);
  if (ed) {
    C.sel = ed.i;
    C.drag = {kind: 'edge', c: C.cuts[ed.i], side: ed.side};
  } else {
    C.drag = {kind: 'new', t0: t, x0: e.clientX, i: C.cuts.findIndex(c => t > c.a && t < c.b), c: null};
  }
  renderCut();
};
track.onpointermove = e => {
  if (!C) return;
  const t = tAt(e), g = C.drag;
  popAt(t, e.clientX);
  if (!g) { track.style.cursor = !C.running && edgeAt(e) ? 'ew-resize' : ''; return; }
  if (g.kind === 'edge') {
    g.c[g.side] = snapEnds(t);
  } else {
    if (!g.c && Math.abs(e.clientX - g.x0) < 4) return;
    if (!g.c) { g.c = {a: g.t0, b: g.t0}; C.cuts.push(g.c); C.sel = C.cuts.length - 1; }
    g.c.a = snapEnds(Math.min(g.t0, t));
    g.c.b = snapEnds(Math.max(g.t0, t));
  }
  renderCut();
};
track.onpointerup = e => {
  const g = C && C.drag;
  if (!g) return;
  C.drag = null;
  if (g.kind === 'new' && !g.c) {  // простой клик: курсор сюда, кусок под ним — выбрать
    C.sel = g.i;
    C.cur = tAt(e);
  }
  normCuts();
  renderCut();
};
track.onpointerleave = () => { if (C && !C.drag) hidePop(); };

function cutKey(e) {
  if (C.running) { if (!(e.ctrlKey || e.metaKey || e.altKey)) e.preventDefault(); return; }
  const step = e.ctrlKey || e.metaKey ? 60 : e.shiftKey ? 10 : 1;
  switch (e.code) {
    case 'ArrowRight': moveCur(C.cur + step); break;
    case 'ArrowLeft': moveCur(C.cur - step); break;
    case 'Home': moveCur(0); break;
    case 'End': moveCur(C.d); break;
    case 'KeyI': C.mark = C.cur; renderCut(); break;
    case 'KeyO': cutOut(); break;
    case 'Delete': case 'Backspace': delCut(); break;
    case 'Escape':
      if (C.mark !== null) C.mark = null;
      else if (C.sel >= 0) C.sel = -1;
      else { closeCut(); break; }
      renderCut();
      break;
    default:
      if (e.ctrlKey || e.metaKey || e.altKey || /^F\d+$/.test(e.key)) return;  // сочетания и F-клавиши — как обычно
  }
  e.preventDefault();  // остальное (пробел, стрелки вверх-вниз, Del…) в режиме обрезки не листает и не удаляет
}

async function startCut() {
  if (!C || C.running || !C.cuts.length) return;
  const it = items.find(x => x.id === C.id), n = C.cuts.length;
  const kept = C.d - C.cuts.reduce((s, c) => s + removedOf(c), 0);
  if (!await ask('Обрезать «' + (it ? full(it) : C.info.file) + '»?\n' +
      'Останется ' + fmtT(kept) + ' из ' + fmtT(C.d) + ' (вырезается ' + n + ' ' + plural(n, ['кусок', 'куска', 'кусков']) + ').\n' +
      'Без перекодирования: оставшиеся куски начинаются с ближайшего ключевого кадра, до пары секунд лишнего может остаться.\n' +
      'Оригинал уйдёт в _на_удаление, Ctrl+Z вернёт его вместе со старым превью. Превью пересоздастся.', 'Обрезать')) return;
  if (!C) return;
  try {
    C.status = await api('/api/cut/start', true, {id: C.id, cuts: C.cuts.map(c => [c.a, c.b])});
    C.running = true;
    C.sel = -1;
    C.mark = null;
    renderCut();
    cutWatch();
  } catch (e) {
    toast('Не обрезано: ' + e.message, true);
  }
}
function cutWatch() { if (!cutTimer) cutTimer = setTimeout(cutTick, 500); }
async function cutTick() {
  cutTimer = 0;
  let s;
  try {
    s = await api('/api/cut');
  } catch (e) {
    cutWatch();
    return;
  }
  if (C && C.id === s.id) { C.status = s; C.running = s.running; renderCut(); }
  if (s.running) { cutWatch(); return; }
  if (s.error) { toast('Не обрезано: ' + s.error, true); return; }
  toast('Обрезано: ' + s.name + '. ' + (s.note || 'Превью пересоздаётся…'), !!s.note);
  if (C && C.id === s.id) closeCut(true);
  await load(s.id).catch(() => {});
}

$('#chead').onclick = () => { if (C.cur > 0.2) addCut(0, C.cur); else toast('Поставьте курсор туда, где начинается нужное'); };
$('#ctail').onclick = () => { if (C.cur < C.d - 0.2) addCut(C.cur, C.d); else toast('Поставьте курсор туда, где кончается нужное'); };
$('#cin').onclick = () => { C.mark = C.cur; renderCut(); };
$('#cout').onclick = cutOut;
$('#cdel').onclick = delCut;
$('#cclr').onclick = () => { C.cuts = []; C.sel = -1; C.mark = null; renderCut(); };
$('#cgo').onclick = startCut;
$('#cstop').onclick = () => api('/api/cut/stop', true).catch(e => toast('Не остановлено: ' + e.message, true));
$('#cexit').onclick = () => closeCut();

/* ───── действия ───── */

async function load(focusId) {
  const j = await api('/api/list');
  all = j.items; videos = j.videos; undoN = j.undo; ROOT = j.root; ROOT_PATH = j.rootPath; recent = j.recent || [];
  rootStat();
  trashInfo = j.trash; ff = j.ff; job = j.job; ign = j.ign || ign; opts = j.opts || opts; mpc = j.mpc || mpc;
  if (!skipLoaded) {
    skipLoaded = true;
    try { skipDirs = new Set(JSON.parse(store.get('skip') || '[]')); } catch (_) { /* пусто */ }
  }
  all.forEach(it => knownDirs.add(it.dir));
  videos.forEach(v => knownDirs.add(v.dir));
  if (focusId !== undefined) {
    const it = all.find(x => x.id === focusId);
    if (it && !inView(it)) folder = it.dir;
  }
  applyView(focusId);
  trashStat();
  if (mode === 'videos') renderVideos();
  renderJob();
  if (!inited) {
    inited = true;
    if (!all.length && videos.length) setMode('videos');
  }
  if (job.running) { wasRunning = true; watchJob(); }
  if (j.cut && j.cut.running) cutWatch();
}

// пометить превью ошибкой и показать её на плитке, в просмотре и во всплывающем сообщении
function failItem(it, msg) {
  it.err = msg;
  const i = items.indexOf(it);
  if (i >= 0) {
    const f = tile(it);
    if (i === cur) f.classList.add('sel');
    grid.replaceChild(f, grid.children[i]);
  }
  if (viewer && items[cur] === it) showViewer();
  else toast('Не удалено: ' + msg, true);
}

async function removeCur() {
  const it = items[cur];
  if (!it || busy) return;
  busy = true;
  if (it.err) {
    it.err = null;
    grid.replaceChild(tile(it), grid.children[cur]);
    select(cur, false);
  }
  const f0 = grid.children[cur];
  f0.classList.add('wait');
  $('#v').classList.add('wait');
  document.body.classList.add('wait');
  try {
    const r = await api('/api/delete/' + it.id, true);
    if (r.trash) { trashInfo = r.trash; trashStat(); }
    const i = items.indexOf(it);          // за время запроса список мог измениться
    const wasCur = i === cur;
    if (i >= 0) {
      items.splice(i, 1);
      grid.children[i].remove();
      if (i < cur) cur--;
    }
    const k = all.indexOf(it);
    if (k >= 0) all.splice(k, 1);
    undoN++;
    stat();
    renderTree();
    if (!wasCur) {
      select(cur, false);
    } else if (viewer && cur >= items.length) {
      // удалили последнее превью в списке: дальше — первое превью следующей папки;
      // если следующей нет — остаёмся на предыдущем (а если список пуст, идём в прошлую папку)
      if (!crossFolder(1, false, true)) {
        if (items.length) {
          select(items.length - 1);
          toast('Удалено. Ctrl+Z вернёт пару');
        } else if (!crossFolder(-1, true, true)) {
          closeViewer();
          toast('Превью закончились');
        }
      }
    } else {
      select(cur);
      if (viewer) toast('Удалено. Ctrl+Z вернёт пару');
    }
  } catch (e) {
    f0.classList.remove('wait');
    failItem(it, e.message);
    if (e.resync) await load(it.id).catch(() => {});
  }
  $('#v').classList.remove('wait');
  document.body.classList.remove('wait');
  busy = false;
}

async function undoLast() {
  if (!undoN || busy) return;
  busy = true;
  try {
    const j = await api('/api/undo', true);
    if (j.trash) { trashInfo = j.trash; trashStat(); }
    await load(j.id);
    select(cur);
    toast('Пара возвращена');
  } catch (e) {
    toast('Не отменено: ' + e.message, true);
    if (e.resync) await load().catch(() => {});
  }
  busy = false;
}

async function openCur() {
  const it = items[cur];
  if (!it || !it.nv) return;
  try {
    await api('/api/open/' + it.id, true);
    toast('Открываю видео');
  } catch (e) {
    toast('Не открыто: ' + e.message, true);
  }
}

/* ───── события ───── */

grid.onclick = e => {
  const f = e.target.closest('figure');
  if (!f) return;
  const i = items.findIndex(x => x.id === +f.dataset.id);
  if (i < 0) return;
  select(i, false);
  if (e.target.closest('.pk')) { togglePick(i, e.shiftKey); return; }
  const b = e.target.closest('button');
  if (b) {
    if (b.dataset.a === 'open') openCur();
    else if (b.dataset.a === 'del') removeCur();
  } else if (e.target.closest('.im')) {
    if (e.shiftKey) togglePick(i, true);
    else if (e.ctrlKey || e.metaKey) togglePick(i, false);
    else openViewer();
  }
};
$('#dirs').onclick = e => {
  const b = e.target.closest('button.dir');
  if (b) setFolder(b.dataset.d);
};
document.addEventListener('click', e => { const b = e.target.closest('button'); if (b) b.blur(); });

$('#prev').onclick = () => go(cur - 1);
$('#next').onclick = () => go(cur + 1);
$('#pdir').onclick = () => crossFolder(-1, false);
$('#ndir').onclick = () => crossFolder(1, false);
$('#vopen').onclick = openCur;
$('#vdel').onclick = removeCur;
$('#vclose').onclick = () => closeViewer();
$('#vi').onclick = () => { if (!C) closeViewer(); };   // клик по открытому на весь экран превью возвращает обычную ленту
$('#vcut').onclick = openCut;
$('#vpk').onclick = () => { if (items[cur]) togglePick(cur, false); };
$('#und').onclick = undoLast;
$('#tg').onclick = () => { treeOn = !treeOn; store.set('tree', treeOn ? '1' : '0'); renderTree(); };

$('#srt').value = sort;
$('#srt').onchange = e => { sort = e.target.value; store.set('srt', sort); applyView(); e.target.blur(); };
$('#deep').checked = deep;
$('#deep').onchange = e => { deep = e.target.checked; store.set('deep', deep ? '1' : '0'); refreshView(); e.target.blur(); };
const sz = $('#sz');
const setW = () => document.documentElement.style.setProperty('--w', sz.value + 'px');
sz.value = store.get('sz') || 480;
setW();
sz.oninput = () => { setW(); store.set('sz', sz.value); };
sz.onchange = () => sz.blur();
document.body.classList.toggle('nobar', store.get('nobar') === '1');

const hdr = $('header');
const setHH = () => document.documentElement.style.setProperty('--hh', hdr.offsetHeight + 'px');
setHH();
addEventListener('resize', setHH);
if (window.ResizeObserver) new ResizeObserver(setHH).observe(hdr);

addEventListener('keydown', e => {
  if (!$('#dlg').hidden) {  // открыто окно подтверждения: Esc — отмена, остальное не трогаем (Enter нажмёт выбранную кнопку)
    if (e.code === 'Escape') { e.preventDefault(); if (ask.cancel) ask.cancel(); }
    return;
  }
  // F5 и Ctrl+R: страница сама ничего не теряет при перезагрузке, но список файлов хранит сервер, поэтому обновляем его
  if (e.code === 'F5' || (e.code === 'KeyR' && (e.ctrlKey || e.metaKey))) {
    e.preventDefault();
    if (!e.repeat) rescan();
    return;
  }
  if (e.target.matches('select,input')) return;
  if (C && viewer) { cutKey(e); return; }
  if (!$('#trashp').hidden || !$('#rootp').hidden) {
    if (e.code === 'Escape') { $('#trashp').hidden = $('#rootp').hidden = true; e.preventDefault(); }
    return;
  }
  if (mode !== 'previews') return;
  const cols = getComputedStyle(grid).gridTemplateColumns.split(' ').length;
  const step = viewer ? 1 : cols;
  switch (e.code) {
    case 'ArrowRight': go(cur + 1); break;
    case 'ArrowLeft': go(cur - 1); break;
    case 'ArrowDown': go(cur + step); break;
    case 'ArrowUp': go(cur - step); break;
    case 'Home': select(0); break;
    case 'End': select(items.length - 1); break;
    case 'Enter': case 'NumpadEnter': openCur(); break;
    case 'Space': viewer ? closeViewer() : openViewer(); break;
    case 'Escape':
      if (viewer) closeViewer();
      else if (picked.size) { picked.clear(); pickStat(); }
      else return;
      break;
    case 'Delete': case 'Backspace':
      if (!e.repeat) { if (!viewer && picked.size) deleteSelected(); else removeCur(); }
      break;
    case 'BracketLeft': crossFolder(-1, false); break;
    case 'BracketRight': case 'PageDown': crossFolder(1, false); break;
    case 'PageUp': crossFolder(-1, false); break;
    case 'KeyX': if (items[cur]) togglePick(cur, false); break;
    case 'KeyA': if (e.ctrlKey || e.metaKey) { items.forEach(i => picked.add(i.id)); pickStat(); } else return; break;
    case 'KeyE': showCur(); break;
    case 'KeyC': if (!viewer) return; openCut(); break;
    case 'KeyI':
      if (!viewer) return;
      document.body.classList.toggle('nobar');
      store.set('nobar', document.body.classList.contains('nobar') ? '1' : '0');
      break;
    case 'KeyZ': if (e.ctrlKey || e.metaKey) undoLast(); else return; break;
    default: return;
  }
  e.preventDefault();
});

/* ───── вкладки ───── */

function setMode(m) {
  if (m === mode) return;
  if (viewer) closeViewer();
  mode = m;
  document.body.classList.toggle('mode-v', m === 'videos');
  $('#tab-p').classList.toggle('on', m === 'previews');
  $('#tab-v').classList.toggle('on', m === 'videos');
  if (m === 'videos') renderVideos();
  else { stat(); select(cur, false); }
  renderTree();
}
function refreshView() {
  if (mode === 'videos') { renderVideos(); renderTree(); } else applyView();
}
$('#tab-p').onclick = () => setMode('previews');
$('#tab-v').onclick = () => setMode('videos');

/* ───── видео без превью ───── */

const isSel = v => sel.has(v.id) ? sel.get(v.id) : !skipDirs.has(v.dir);
const saveSkip = () => store.set('skip', JSON.stringify([...skipDirs]));

function vrow(v) {
  const bad = job.failed[v.id];
  return '<div class="vr' + (bad ? ' bad' : '') + '" data-id="' + v.id + '">' +
    '<label><input type="checkbox" data-v="' + v.id + '"' + (isSel(v) ? ' checked' : '') + '>' +
    '<span class="vn" title="' + esc(full({dir: v.dir, name: v.file || v.name})) + '">' + esc(v.file || v.name) + '</span></label>' +
    '<span class="vs">' + fmtSize(v.size) + '</span><span class="vd">' + fmtDate(v.mtime) + '</span>' +
    '<button data-a="play" title="Открыть видео в плеере">Открыть</button>' +
    (bad ? '<div class="verr">' + esc(bad) + '</div>' : '') + '</div>';
}

function renderVideos() {
  const list = videos.filter(inView).sort(byName);
  const groups = [], at = new Map();
  for (const v of list) {
    if (!at.has(v.dir)) { at.set(v.dir, groups.length); groups.push({d: v.dir, arr: []}); }
    groups[at.get(v.dir)].arr.push(v);
  }
  $('#vrows').innerHTML = groups.map(g => {
    const n = g.arr.length, s = g.arr.filter(isSel).length;
    return '<div class="grp"><label class="gh"><input type="checkbox" data-g="' + esc(g.d) + '" data-n="' + n + '" data-s="' + s + '"' +
      (s === n ? ' checked' : '') + '><span>' + esc(g.d || ROOT) + '</span><span class="gc">' + n + '</span>' +
      (skipDirs.has(g.d) ? '<span class="tag">превью не создавать</span>' : '') + '</label>' +
      g.arr.map(vrow).join('') + '</div>';
  }).join('') || '<p class="dim pad">' +
    (videos.length ? 'В этой папке нет видео без превью.' : 'У всех видео есть превью.') + '</p>';
  document.querySelectorAll('#vrows input[data-g]').forEach(cb => {
    const s = +cb.dataset.s;
    cb.indeterminate = s > 0 && s < +cb.dataset.n;
  });
  vstat();
}

function vstat() {
  const list = videos.filter(inView), picked = list.filter(isSel);
  $('#vsel').textContent = 'Выбрано ' + picked.length + ' из ' + list.length;
  if (mode === 'videos') {
    $('#cnt').textContent = list.length + ' видео без превью' + (list.length !== videos.length ? ' из ' + videos.length : '');
  }
  const b = $('#vmake');
  b.disabled = !picked.length || job.running || !ff.ok;
  b.textContent = job.running ? 'Идёт создание…' : 'Создать превью' + (picked.length ? ' (' + picked.length + ')' : '');
  const note = $('#vnote');
  if (!ff.ok) {
    note.hidden = false;
    note.innerHTML = 'Для создания превью нужен ffmpeg, но он не найден. Установите его (в Windows: ' +
      '<code>winget install Gyan.FFmpeg</code>), откройте терминал заново и перезапустите скрипт. ' +
      'Если ffmpeg уже установлен, но не добавлен в PATH, запустите скрипт с параметром ' +
      '<code>--ffmpeg "C:\\путь\\ffmpeg.exe"</code>.';
  } else if (!ff.drawtext) {
    note.hidden = false;
    note.textContent = 'В этой сборке ffmpeg нет подписей на кадрах (фильтр drawtext или шрифт не найдены): ' +
      'превью будут без времени и заголовка. Шрифт можно указать параметром --font ПУТЬ.';
  } else {
    note.hidden = true;
  }
  $('#vfmt').textContent = 'Формат превью: сетка ' + opts.cols + '×' + opts.rows + ', ширина ' + opts.width +
    ' px, ' + (opts.header ? 'заголовок и таймкоды' : 'только таймкоды') + '. Меняется параметрами --cols --rows --width --header. Декодирование видео: ' + (opts.hw || 'процессор') + '.';
  const g = $('#vign');
  g.hidden = !ign.files;
  g.textContent = ign.files ? 'Игнорируются файлы ' + ign.exts.join(', ') + ': пропущено ' + ign.files +
    '. Список расширений задаёт параметр --ignore-ext.' : '';
}

function redoStat() {
  const n = items.filter(i => i.nv).length, b = $('#redo');
  b.hidden = !n || mode !== 'previews' || !ff.ok;
  b.disabled = job.running;
  b.textContent = 'Пересоздать превью (' + n + ')';
  const k = items.filter(i => !i.nv).length, o = $('#orph');
  o.hidden = !k || mode !== 'previews';
  o.textContent = 'Убрать превью без видео (' + k + ')';
}

function renderJob() {
  const j = job, fails = Object.keys(j.failed).length;
  $('#jobbar').hidden = !(j.running || j.total);
  $('#vbar').style.width = (j.total ? Math.round(100 * j.done / j.total) : 0) + '%';
  let t = (j.redo ? 'Пересоздано ' : 'Создано ') + j.ok + ' из ' + j.total;
  if (fails) t += ', ошибок: ' + fails;
  if (j.running && j.active.length) t += '. Сейчас: ' + j.active.slice(0, 2).join(', ');
  if (j.running && j.done >= 3) t += '. Осталось около ' + fmtEta(j.elapsed / j.done * (j.total - j.done));
  if (!j.running && j.total) t = (j.stopped ? 'Остановлено. ' : 'Готово. ') + t;
  $('#vptxt').textContent = t;
  $('#vstop').hidden = !j.running;
  vstat();
  redoStat();
}

async function startMake(ids, redo) {
  if (!ids) ids = videos.filter(inView).filter(isSel).map(v => v.id);
  if (!ids.length) return;
  try {
    job = await api('/api/make', true, {ids, redo: !!redo});
    wasRunning = true;
    lastFail = 0;
    renderVideos();
    renderJob();
    watchJob();
  } catch (e) {
    toast('Не запущено: ' + e.message, true);
  }
}
async function stopMake() {
  try { job = await api('/api/make/stop', true); renderJob(); } catch (e) { toast('Не остановлено: ' + e.message, true); }
}
function watchJob() { if (!jobTimer) jobTimer = setTimeout(tickJob, 1000); }
async function tickJob() {
  jobTimer = 0;
  try {
    const prevOk = job.ok;
    job = await api('/api/make');
    renderJob();
    if (job.ok !== prevOk || !job.running) await load();   // появились новые превью — обновить списки
    const fails = Object.keys(job.failed).length;
    if (fails !== lastFail) { lastFail = fails; if (mode === 'videos') renderVideos(); }
    if (job.running) {
      watchJob();
    } else if (wasRunning) {
      wasRunning = false;
      renderJob();
      toast((job.stopped ? 'Остановлено. ' : 'Готово. ') + (job.redo ? 'Пересоздано превью: ' : 'Создано превью: ') + job.ok +
        (fails ? ', ошибок: ' + fails + ' (отмечены красным в списке)' : ''), fails > 0);
    }
  } catch (e) {
    toast('Нет связи с сервером: ' + e.message, true);
  }
}

$('#vrows').onchange = e => {
  const t = e.target;
  if (t.dataset.v !== undefined) {
    sel.set(+t.dataset.v, t.checked);
  } else if (t.dataset.g !== undefined) {
    // галочка папки: включает или исключает её (и, если показаны подпапки, вложенные папки в списке)
    const d = t.dataset.g, dirs = new Set(videos.filter(inView).map(v => v.dir));
    const inside = x => x === d || (deep && (d === '' || x.startsWith(d + '/')));
    dirs.forEach(x => {
      if (!inside(x)) return;
      if (t.checked) skipDirs.delete(x); else skipDirs.add(x);
    });
    videos.filter(v => dirs.has(v.dir) && inside(v.dir)).forEach(v => sel.delete(v.id));
    saveSkip();
  }
  renderVideos();
};
$('#vrows').onclick = e => {
  const b = e.target.closest('button[data-a="play"]');
  if (!b) return;
  api('/api/open/' + b.closest('.vr').dataset.id, true)
    .then(() => toast('Открываю видео'))
    .catch(err => toast('Не открыто: ' + err.message, true));
};
$('#vall').onclick = () => {
  videos.filter(inView).forEach(v => { if (!skipDirs.has(v.dir)) sel.delete(v.id); });
  renderVideos();
};
$('#vnone').onclick = () => {
  videos.filter(inView).forEach(v => sel.set(v.id, false));
  renderVideos();
};
$('#vmake').onclick = () => startMake();
$('#redo').onclick = async () => {
  const ids = items.filter(i => i.nv).map(i => i.id);
  if (!ids.length || job.running) return;
  const where = folder ? 'в папке «' + folder + '»' + (deep ? ' и подпапках' : '') : 'во всех папках';
  const yes = await ask('Пересоздать превью ' + where + ': ' + ids.length + ' шт.?\n\nФормат: сетка ' + opts.cols + '×' + opts.rows + ', ' +
    opts.width + ' px, ' + (opts.header ? 'с заголовком' : 'только таймкоды') + '.\nСтарые превью будут перенесены в _на_удаление, видео не затрагиваются.', 'Пересоздать');
  if (yes) startMake(ids, true);
};
$('#vstop').onclick = stopMake;

/* ───── папка «на удаление» ───── */

let trashTimer = 0;
function trashStat() {
  const n = trashInfo.files, b = $('#trash');
  b.hidden = !n;
  b.textContent = 'На удаление: ' + n + ' ' + plural(n, ['файл', 'файла', 'файлов']) + ', ' + fmtSize(trashInfo.bytes) +
    (trashInfo.pending ? ' (считаю…)' : '');
  if (!n) $('#trashp').hidden = true;
  if (trashInfo.pending && !trashTimer) {   // подсчёт идёт на сервере в фоне (по сети он долгий): спрашиваем, пока не закончится
    trashTimer = setTimeout(async () => {
      trashTimer = 0;
      try { trashInfo = await api('/api/trash'); } catch (_) { return; }
      trashStat();
    }, 2000);
  }
}
/* ───── открытая папка: недавние и выбор другой ───── */

function rootStat() {
  const b = $('#rootb');
  b.textContent = 'Папка: ' + (ROOT || '—') + ' ▾';
  b.title = 'Открыта папка ' + ROOT_PATH + '. Нажмите, чтобы открыть другую';
  document.title = 'Video Manager' + (ROOT ? ' — ' + ROOT : '');
}
$('#rootb').onclick = () => {
  const p = $('#rootp');
  p.hidden = !p.hidden;
  if (p.hidden) return;
  $('#trashp').hidden = true;
  $('#rooti').textContent = ROOT_PATH;
  $('#rootl').innerHTML = recent.map((r, i) => '<button data-i="' + i + '" title="Открыть эту папку">' + esc(r.name) +
    '<span class="dim">' + esc(r.folder) + '</span></button>').join('');
  $('#rootl').hidden = !recent.length;
};
$('#rcancel').onclick = () => { $('#rootp').hidden = true; };
async function openRoot(path, body) {
  if (job.running) { toast('Идёт создание превью: дождитесь конца или остановите его', true); return; }
  $('#rootp').hidden = true;
  if (undoN && !await ask('В другой папке Ctrl+Z не вернёт то, что удалено здесь (файлы останутся в _на_удаление этой папки). Открыть другую папку?', 'Открыть')) return;
  $('#rootb').disabled = true;
  toast(body ? 'Читаю папку…' : 'Выберите папку в окне выбора…');
  try {
    await store.flush();
    const r = await api(path, true, body);
    if (r.ok) { location.reload(); return; }  // настройки страницы свои у каждой папки: проще загрузить её заново
    toast('Папка не выбрана');
  } catch (e) {
    toast('Не открыто: ' + e.message, true);
  }
  $('#rootb').disabled = false;
}
$('#rpick').onclick = () => openRoot('/api/root/pick');
$('#rootl').onclick = e => {
  const b = e.target.closest('button[data-i]');
  if (b) openRoot('/api/root/recent', {folder: recent[+b.dataset.i].folder});
};

$('#trash').onclick = () => {
  const p = $('#trashp');
  p.hidden = !p.hidden;
  if (!p.hidden) $('#rootp').hidden = true;
  if (!p.hidden) {
    const n = trashInfo.files;
    $('#trashi').textContent = 'В папке _на_удаление: ' + n + ' ' + plural(n, ['файл', 'файла', 'файлов']) + ', ' +
      fmtSize(trashInfo.bytes) + '. После удаления насовсем вернуть их будет нельзя, Ctrl+Z тоже перестанет работать.';
  }
};
$('#tcancel').onclick = () => { $('#trashp').hidden = true; };
$('#topen').onclick = () => {
  api('/api/trash/open', true).catch(e => toast('Не открыто: ' + e.message, true));
};
$('#tpurge').onclick = async () => {
  const b = $('#tpurge');
  b.disabled = true;
  try {
    const r = await api('/api/purge', true);
    trashInfo = r.trash;
    undoN = 0;
    stat();
    trashStat();
    $('#trashp').hidden = true;
    const bad = r.failed.length;
    toast('Удалено насовсем: ' + r.removed + ' ' + plural(r.removed, ['файл', 'файла', 'файлов']) + ', освобождено ' +
      fmtSize(r.bytes) + (bad ? '. Не удалось удалить: ' + bad + ' (' + r.failed[0].error + ')' : ''), bad > 0);
  } catch (e) {
    toast('Не очищено: ' + e.message, true);
  }
  b.disabled = false;
};

/* ───── обновить список файлов ───── */

async function rescan() {
  if (refreshing) return;
  refreshing = true;
  const b = $('#refresh');
  b.disabled = true;
  b.textContent = 'Обновляю…';
  try {
    const r = await api('/api/rescan', true);
    await load();
    const add = [];
    if (r.added_videos) add.push(r.added_videos + ' ' + plural(r.added_videos, ['новое видео', 'новых видео', 'новых видео']));
    if (r.added_previews) add.push(r.added_previews + ' ' + plural(r.added_previews, ['новое превью', 'новых превью', 'новых превью']));
    if (r.gone) add.push('пропало файлов: ' + r.gone);
    toast(add.length ? 'Обновлено: ' + add.join(', ') : 'Обновлено: изменений нет');
  } catch (e) {
    toast('Не обновлено: ' + e.message, true);
  }
  b.disabled = false;
  b.textContent = 'Обновить';
  refreshing = false;
}
$('#refresh').onclick = rescan;

/* ───── превью без видео ───── */

$('#orph').onclick = async () => {
  const list = items.filter(i => !i.nv);
  if (!list.length) return;
  const where = folder ? 'в папке «' + folder + '»' + (deep ? ' и подпапках' : '') : 'во всех папках';
  const yes = await ask('Убрать превью без видео ' + where + ': ' + list.length + ' шт.?\n\nФайлы переедут в _на_удаление, видео не затрагиваются.\nCtrl+Z вернёт их все сразу.', 'Убрать');
  if (!yes) return;
  $('#orph').disabled = true;
  try {
    const r = await api('/api/orphans', true, {ids: list.map(i => i.id)});
    trashInfo = r.trash;
    await load();
    const bad = r.failed.length;
    toast('Перенесено в _на_удаление: ' + r.removed + ' ' + plural(r.removed, ['превью', 'превью', 'превью']) +
      (bad ? '. Не удалось: ' + bad + ' (' + r.failed[0].error + ')' : '. Ctrl+Z вернёт их'), bad > 0);
  } catch (e) {
    toast('Не убрано: ' + e.message, true);
  }
  $('#orph').disabled = false;
};

/* ───── окно подтверждения (системное confirm() в окне приложения не гарантировано) ───── */

function ask(text, okLabel) {
  return new Promise(res => {
    const d = $('#dlg');
    $('#dtxt').textContent = text;
    $('#dok').textContent = okLabel || 'Продолжить';
    d.hidden = false;
    $('#dok').focus();
    const done = v => { d.hidden = true; ask.cancel = null; res(v); };
    $('#dok').onclick = () => done(true);
    $('#dno').onclick = () => done(false);
    ask.cancel = () => done(false);
  });
}

/* ───── выбранная папка: проводник и плейлист MPC ───── */

const videoCount = () => all.filter(inView).reduce((s, i) => s + i.nv, 0) + videos.filter(inView).length;
function folderStat() {
  $('#fdel').disabled = !folder;
  const n = videoCount(), name = mpc.name || 'MPC';
  const tip = mpc.ok ? '' : 'MPC не найден: укажите путь параметром --player или в pairview.json';
  const p = $('#fplay'), b = $('#fmpc');
  p.textContent = 'Воспроизвести в ' + name + ' (' + n + ')';
  p.disabled = b.disabled = !n;
  p.title = tip || 'Запустить все видео выбранной папки' + (deep ? ' и подпапок' : '') + ' в ' + name +
    ': плейлист заменится и воспроизведение начнётся сразу (как «Play with MPC-HC» в проводнике)';
  b.title = tip || 'Дописать видео в конец плейлиста ' + name + ', не запуская воспроизведение (как «Add to playlist»)';
}
async function mpcSend(body, add) {
  try {
    const r = await api('/api/mpc', true, Object.assign({add}, body));
    toast((add ? 'В плейлист ' + mpc.name + ' добавлено видео: ' : 'Запускаю в ' + mpc.name + ', видео: ') + r.added +
      (r.calls > 1 ? ' (несколькими запросами: длинный список)' : ''));
  } catch (e) {
    toast('Не получилось: ' + e.message, true);
  }
  folderStat();
}
$('#fplay').onclick = () => mpcSend({dir: folder, deep}, false);
$('#fmpc').onclick = () => mpcSend({dir: folder, deep}, true);
$('#fexp').onclick = () => {
  api('/api/explorer', true, {dir: folder}).catch(e => toast('Не открыто: ' + e.message, true));
};
function showCur() {
  const it = items[cur];
  if (!it) return;
  api('/api/explorer', true, {id: it.id}).catch(e => toast('Не открыто: ' + e.message, true));
}
addEventListener('contextmenu', e => { if (window.pywebview) e.preventDefault(); });

/* ───── выделение плиток: удалить пары, пересоздать превью, играть в MPC — только выбранные ───── */

function pickStat() {
  grid.querySelectorAll('figure').forEach(f => f.classList.toggle('pick', picked.has(+f.dataset.id)));
  document.body.classList.toggle('picking', picked.size > 0);
  const sel = items.filter(i => picked.has(i.id)), n = sel.length, withVideo = sel.filter(i => i.nv).length;
  $('#selbar').hidden = !n;
  $('#selcnt').textContent = 'Выбрано: ' + n;
  $('#sdel').textContent = 'Удалить пары (' + n + ')';
  $('#sredo').textContent = 'Пересоздать превью (' + withVideo + ')';
  $('#sredo').disabled = !withVideo || job.running || !ff.ok;
  $('#splay').textContent = 'Воспроизвести в MPC (' + withVideo + ')';
  $('#splay').disabled = !withVideo;
  if (viewer && items[cur]) $('#vpk').textContent = picked.has(items[cur].id) ? '✓ Выбрано' : 'Выбрать (X)';
}

function togglePick(i, range) {
  if (!items[i]) return;
  if (range && anchor >= 0 && anchor < items.length) {
    const lo = Math.min(anchor, i), hi = Math.max(anchor, i);
    for (let k = lo; k <= hi; k++) picked.add(items[k].id);
  } else {
    const id = items[i].id;
    if (picked.has(id)) picked.delete(id); else picked.add(id);
    anchor = i;
  }
  pickStat();
}

async function deleteSelected() {
  const ids = items.filter(i => picked.has(i.id)).map(i => i.id);
  if (!ids.length || busy) return;
  busy = true;
  const at = cur;
  try {
    const r = await api('/api/delete-many', true, {ids});
    trashInfo = r.trash;
    picked.clear();
    await load();
    select(Math.min(at, items.length - 1));
    const bad = r.failed.length;
    toast('Перенесено в _на_удаление: ' + r.removed + ' ' + plural(r.removed, ['пара', 'пары', 'пар']) +
      (bad ? '. Не удалось: ' + bad + ' (' + r.failed[0].error + ')' : '. Ctrl+Z вернёт их все сразу'), bad > 0);
  } catch (e) {
    toast('Не удалено: ' + e.message, true);
  }
  busy = false;
  pickStat();
}

$('#sdel').onclick = deleteSelected;
$('#sall').onclick = () => { items.forEach(i => picked.add(i.id)); pickStat(); };
$('#snone').onclick = () => { picked.clear(); pickStat(); };
$('#sredo').onclick = async () => {
  const ids = items.filter(i => picked.has(i.id) && i.nv).map(i => i.id);
  if (!ids.length || job.running) return;
  const yes = await ask('Пересоздать превью выбранных: ' + ids.length + ' шт.?\n\nФормат: сетка ' + opts.cols + '×' + opts.rows + ', ' +
    opts.width + ' px, ' + (opts.header ? 'с заголовком' : 'только таймкоды') +
    '.\nСтарые превью будут перенесены в _на_удаление, видео не затрагиваются.', 'Пересоздать');
  if (yes) { picked.clear(); pickStat(); startMake(ids, true); }
};
$('#splay').onclick = () => {
  const ids = items.filter(i => picked.has(i.id) && i.nv).map(i => i.id);
  if (ids.length) mpcSend({ids}, false);
};

/* ───── удаление папок: выбранной целиком и пустых (всё уходит в _на_удаление, Ctrl+Z возвращает) ───── */

function forgetDir(rel) {
  [...knownDirs].forEach(d => { if (d === rel || d.startsWith(rel + '/')) knownDirs.delete(d); });
  if (folder === rel || folder.startsWith(rel + '/')) folder = rel.includes('/') ? rel.slice(0, rel.lastIndexOf('/')) : '';
}

$('#fdel').onclick = async () => {
  if (!folder) return;
  const target = folder;
  let info;
  try {
    info = await api('/api/folder/info', true, {dir: target});
  } catch (e) {
    toast('Папку не удалось осмотреть: ' + e.message, true);
    return;
  }
  const parts = [];
  if (info.pairs) parts.push(info.pairs + ' ' + plural(info.pairs, ['пара', 'пары', 'пар']));
  if (info.videos_only) parts.push(info.videos_only + ' видео без превью');
  if (info.previews_only) parts.push(info.previews_only + ' превью без видео');
  if (info.other) parts.push(info.other + ' ' + plural(info.other, ['другой файл', 'других файла', 'других файлов']));
  const yes = await ask('Удалить папку «' + target + '» целиком?\n\nВнутри: ' + (parts.join(', ') || 'файлов нет') +
    '; подпапок: ' + info.dirs + '. Всего ' + fmtSize(info.bytes) + '.\n\nПапка переедет в _на_удаление вместе с подпапками ' +
    'и всеми файлами (галочка «включая подпапки» не влияет). Ctrl+Z вернёт её.', 'Удалить папку');
  if (!yes) return;
  try {
    const r = await api('/api/folder/delete', true, {dir: target});
    trashInfo = r.trash;
    forgetDir(target);
    await load();
    toast('Папка «' + target + '» перенесена в _на_удаление. Ctrl+Z вернёт её');
  } catch (e) {
    toast('Не удалено: ' + e.message, true);
  }
};

$('#fempty').onclick = async () => {
  let r;
  try {
    r = await api('/api/empty', true, {});
  } catch (e) {
    toast('Не удалось найти пустые папки: ' + e.message, true);
    return;
  }
  if (!r.dirs.length) { toast('Пустых папок нет'); return; }
  const shown = r.dirs.slice(0, 25).map(d => '• ' + d).join('\n') + (r.dirs.length > 25 ? '\n… и ещё ' + (r.dirs.length - 25) : '');
  const yes = await ask('Пустые папки (без файлов): ' + r.dirs.length + ' шт.\n\n' + shown +
    '\n\nОни переедут в _на_удаление. Ctrl+Z вернёт их.', 'Убрать ' + r.dirs.length);
  if (!yes) return;
  try {
    const d = await api('/api/empty/delete', true, {dirs: r.dirs});
    trashInfo = d.trash;
    r.dirs.forEach(forgetDir);
    await load();
    const bad = d.failed.length;
    toast('Пустых папок перенесено: ' + d.removed + (bad ? '. Не удалось: ' + bad + ' (' + d.failed[0].error + ')' : '. Ctrl+Z вернёт их'), bad > 0);
  } catch (e) {
    toast('Не убрано: ' + e.message, true);
  }
};

load().catch(e => toast(e.message, true));
</script>
</body>
</html>
"""


# ───────────────────────── запуск ─────────────────────────

def die(msg):
    """Сообщить об ошибке и выйти. Без консоли (pythonw) текст показывается окном сообщения: иначе его никто не увидит."""
    print(msg, file=sys.stderr)
    if os.name == 'nt' and not HAS_CONSOLE[0]:
        try:
            import ctypes
            ctypes.windll.user32.MessageBoxW(0, str(msg), 'pairview', 0x10)
        except Exception:  # noqa: BLE001
            pass
    sys.exit(1)


def setup_log():
    """Запуск через pythonw: консоли нет, sys.stdout пуст. Пишем в журнал рядом с настройками."""
    if sys.stdout is not None and sys.stderr is not None:
        return
    HAS_CONSOLE[0] = False
    try:
        os.makedirs(app_dir(), exist_ok=True)
        path = os.path.join(app_dir(), 'pairview.log')
        if os.path.exists(path) and os.path.getsize(path) > 1_000_000:
            os.remove(path)
        log = open(path, 'a', encoding='utf-8', buffering=1)
        sys.stdout = sys.stderr = log
        print('\n=== запуск %s ===' % time.strftime('%Y-%m-%d %H:%M:%S'))
    except OSError:
        pass


def load_config():
    """Постоянные параметры из pairview.json (рядом со скриптом или в папке настроек). Командная строка важнее."""
    for base in (base_dir(), app_dir()):
        path = os.path.join(base, 'pairview.json') if base else ''
        if path and os.path.isfile(path):
            try:
                with open(path, encoding='utf-8') as f:
                    cfg = json.load(f)
                if isinstance(cfg, dict):
                    return cfg, path
                print('Файл %s: ожидался объект {"параметр": значение}, пропущен.' % path)
            except (OSError, ValueError) as e:
                print('Файл %s не прочитан: %s' % (path, e))
    return {}, ''


def pick_folder(initial=''):
    """Диалог выбора папки (tkinter входит в состав Python). Пусто — если диалог недоступен или отменён."""
    try:
        import tkinter
        from tkinter import filedialog
        root = tkinter.Tk()
        root.withdraw()
        root.attributes('-topmost', True)
        try:
            return filedialog.askdirectory(title='Папка с видео и превью', initialdir=initial or None, mustexist=True) or ''
        finally:
            root.destroy()
    except Exception:  # noqa: BLE001 — нет tkinter или дисплея
        return ''


def main():
    global ROOT_NAME, VROOT, PROOT
    setup_log()
    ap = argparse.ArgumentParser(description='Video Manager: просмотр превью, выборочное удаление, создание превью, запуск в MPC.')
    ap.add_argument('folder', nargs='?',
                    help='папка с видео (и с превью, если они лежат вместе); подпапки учитываются. '
                         'Без неё открывается папка прошлого запуска, если её нет — folder из pairview.json, '
                         'иначе диалог выбора папки')
    ap.add_argument('--previews', metavar='ПАПКА', help='отдельная папка с превью (подпапки те же, что у видео)')
    ap.add_argument('--clean', choices=['videos', 'previews'],
                    help='videos — файлы видео без превью; previews — превью без видео')
    ap.add_argument('--apply', action='store_true', help='с --clean: реально перенести в %s' % TRASH)
    ap.add_argument('--purge', action='store_true', help='удалить насовсем всё, что лежит в %s' % TRASH)
    ap.add_argument('--ffmpeg', metavar='ПУТЬ', help='путь к ffmpeg (файлу или папке), если его нет в PATH')
    ap.add_argument('--font', metavar='ПУТЬ', help='файл шрифта .ttf для подписей на превью')
    ap.add_argument('--player', metavar='ПУТЬ',
                    help='путь к mpc-hc64.exe / mpc-be64.exe для кнопки «В плейлист MPC» '
                         '(по умолчанию ищется MPC-HC из K-Lite и в стандартных папках)')
    ap.add_argument('--cols', type=int, default=10, help='столбцов кадров в превью (по умолчанию 10)')
    ap.add_argument('--rows', type=int, default=9, help='строк кадров в превью (по умолчанию 9)')
    ap.add_argument('--width', type=int, default=2560, help='ширина превью в пикселях (по умолчанию 2560, под 2K-монитор)')
    ap.add_argument('--header', action='store_true', help='добавить сверху заголовок с данными о файле (по умолчанию только таймкоды)')
    ap.add_argument('--gpu', choices=['auto', 'on', 'off'], default='auto',
                    help='видеокарта NVIDIA: on — декодировать на ней (для превью обычно не ускоряет: время уходит на запуск ffmpeg и чтение диска), auto и off — процессор')
    ap.add_argument('--jobs', type=int, default=OPTS['jobs'],
                    help='сколько видео обрабатывать одновременно (по умолчанию %d: половина ядер процессора)' % OPTS['jobs'])
    ap.add_argument('--ignore-ext', default='ts', metavar='СПИСОК',
                    help='расширения видео, которые игнорировать, через запятую (по умолчанию ts); '
                         'пустая строка — ничего не игнорировать')
    ap.add_argument('--per-frame', action='store_true',
                    help='брать кадры превью по одному, а не пачками (медленнее; на случай, если пачки не работают)')
    ap.add_argument('--port', type=int, default=0,
                    help='порт локального сервера (по умолчанию выбирается свободный: окна на разных папках не мешают друг другу)')
    ap.add_argument('--browser', action='store_true', help='открыть галерею в браузере, а не в своём окне (pywebview)')
    ap.add_argument('--no-browser', action='store_true', help='ничего не открывать (только сервер)')

    cfg, cfg_path = load_config()
    known = {x.dest for x in ap._actions}
    unknown = sorted(k for k in cfg if k not in known)
    if unknown:
        print('В %s неизвестные параметры (пропущены): %s' % (cfg_path, ', '.join(unknown)))
    cfg_folder = cfg.pop('folder', None)  # папка из файла — запасная: важнее папка прошлого запуска
    ap.set_defaults(**{k: v for k, v in cfg.items() if k in known})
    a = ap.parse_args()

    if not a.folder:
        last, last_p = last_root()
        if last:
            a.folder = last
            # previews из pairview.json относится к папке из файла; у папки прошлого запуска — своя
            if not any(x == '--previews' or x.startswith('--previews=') for x in sys.argv[1:]):
                a.previews = last_p or None
            print('Папка прошлого запуска: ' + last)
        elif isinstance(cfg_folder, str) and cfg_folder:
            a.folder = cfg_folder
        else:
            a.folder = pick_folder()
        if not a.folder:
            die('Не указана папка. Запустите: pairview.py "D:\\Видео" — или впишите "folder" в pairview.json.')
    vroot = os.path.abspath(a.folder)
    proot = os.path.abspath(a.previews) if a.previews else vroot
    for r in (vroot, proot):
        if not os.path.isdir(r):
            die('Нет такой папки: ' + r)
    VROOT, PROOT = vroot, proot
    ROOT_NAME = os.path.basename(vroot) or vroot
    remember_folder(vroot, proot)

    if a.purge:
        refresh_trash_stats(wait=True)
        st = trash_stats()
        if not st['files']:
            print('В %s пусто.' % TRASH)
            return
        print('В %s: файлов %d, всего %s.' % (' и '.join(trash_dirs()), st['files'], human_size(st['bytes'])))
        if input('Удалить насовсем? Вернуть их будет нельзя. [д/Н] ').strip().lower() not in ('д', 'да', 'y', 'yes'):
            print('Отменено.')
            return
        r = purge()
        print('Удалено файлов: %d, освобождено %s.' % (r['removed'], human_size(r['bytes'])))
        for f in r['failed'][:20]:
            print('  не удалось:', f['path'], '—', f['error'])
        return

    OPTS.update(cols=max(1, min(a.cols, 20)), rows=max(1, min(a.rows, 20)), header=a.header,
                width=max(640, min(a.width, 7680)), jobs=max(1, min(a.jobs, 16)))
    GPU['mode'] = a.gpu
    FAST['on'] = not a.per_frame
    detect_ff(a.ffmpeg, a.font)
    PLAYER['path'] = find_player(a.player)
    if a.player and not PLAYER['path']:
        print('Предупреждение: плеер из --player не найден: %s' % a.player)
    wanted = {'.' + x.strip().lstrip('.').lower()
              for x in a.ignore_ext.replace(';', ',').replace(' ', ',').split(',') if x.strip().strip('.')}
    if wanted - VIDEO:
        print('Предупреждение: %s и так не считаются видео, игнорировать нечего.' % ', '.join(sorted(wanted - VIDEO)))
    IGNORE.clear()
    IGNORE.update(wanted & VIDEO)

    groups = scan(vroot, proot)
    pairs = sum(1 for g in groups.values() if g['v'] and g['p'])
    only_p = sum(1 for g in groups.values() if g['p'] and not g['v'])
    only_v = sum(1 for g in groups.values() if g['v'] and not g['p'])
    print('Пар: %d, превью без видео: %d, видео без превью: %d' % (pairs, only_p, only_v))
    if IGNORE:
        print('Игнорируются файлы %s: пропущено %d (параметр --ignore-ext)' % (', '.join(sorted(IGNORE)), SCAN['ignored']))
    if not groups:
        msg = ('Ни видео, ни превью не найдено в %s: проверьте путь к папке.' % vroot +
               (' Все найденные видеофайлы (%d) игнорируются из-за --ignore-ext.' % SCAN['ignored'] if SCAN['ignored'] else ''))
        if a.clean:
            die(msg)
        print(msg + ' Другую папку можно открыть кнопкой в шапке.')  # не выходим: пустая папка прошлого запуска иначе не даст запуститься

    if a.clean:
        if not pairs:
            die('Ни одной пары не найдено: проверьте имена файлов и (при --previews) одинаковые подпапки.')
        src, other = ('v', 'p') if a.clean == 'videos' else ('p', 'v')
        files = [f for g in groups.values() if g[src] and not g[other] for f in g[src]]
        print('Без пары (%s): %d' % ('видео' if src == 'v' else 'превью', len(files)))
        for f in files[:20]:
            print('  ', f[0])
        if len(files) > 20:
            print('   … и ещё', len(files) - 20)
        if not files:
            return
        if not a.apply:
            print('Пробный запуск, ничего не перенесено. Для переноса добавьте --apply.')
            return
        if input('Перенести %d файл(ов) в %s? [д/Н] ' % (len(files), TRASH)).strip().lower() not in ('д', 'да', 'y', 'yes'):
            print('Отменено.')
            return
        for f in files:
            to_trash(f[0], f[1])
        print('Готово.')
        return

    if FF['ok']:
        print('ffmpeg: %s%s' % (FF['version'] or 'найден', '' if FF['drawtext'] and FF['font']
                                else ' (без подписей на кадрах: нет drawtext или шрифта, см. --font)'))
        print('Декодирование видео: ' + gpu_info())
    else:
        print('ffmpeg не найден — создание превью недоступно (подсказка есть в интерфейсе).')
    print('Плеер для плейлиста: ' + (PLAYER['path'] or 'MPC не найден (кнопка «В плейлист MPC» не заработает; см. --player)'))
    for gid, key in enumerate(sorted(groups)):
        GROUPS[gid] = groups[key]
    IDS['next'] = len(groups)
    refresh_trash_stats()  # счёт файлов в _на_удаление идёт в фоне: по сети он может занять минуты
    try:
        srv = Server(('127.0.0.1', a.port), Handler)
    except OSError:
        srv = Server(('127.0.0.1', 0), Handler)
    url = 'http://127.0.0.1:%d/?t=%s' % (srv.server_address[1], TOKEN)
    print('Галерея:', url)
    print('«Удалить пару» переносит файлы в', TRASH)
    try:
        if a.no_browser:
            print('Выход — Ctrl+C.')
            srv.serve_forever()
        elif a.browser:
            print('Выход — Ctrl+C.')
            webbrowser.open(url)
            srv.serve_forever()
        else:
            threading.Thread(target=srv.serve_forever, daemon=True).start()
            if run_window(url, 'Video Manager — ' + ROOT_NAME):
                print('Окно закрыто.')
            else:
                print('Выход — Ctrl+C.')
                webbrowser.open(url)
                while True:
                    time.sleep(3600)
    except KeyboardInterrupt:
        pass
    finally:
        stop_job()
        time.sleep(0.5)


if __name__ == '__main__':
    main()
