#!/usr/bin/env python3
"""CatN64Emu 0.1.1a — N64 ROM launcher inspired by Parallel Launcher.
© AC Kondo 1999–2026. RetroArch/libretro backend with portable runtime support.

0.1.1a
  * Tools -> Install Native RetroArch: downloads the official RetroArch build
    that matches this computer into catn64emu_runtime/ and pairs it with a
    matching N64 core:
      macOS   Universal (Apple M-series native + Intel)   RetroArch_Metal.dmg
      Windows x86_64 / x86 (ARM64 runs x86_64 via emulation)   RetroArch.7z
      Linux   x86_64 / aarch64 (AppImage), Flatpak fallback      RetroArch.7z
    Offered automatically when RetroArch is missing, or when an Intel-only
    RetroArch is found on an Apple Silicon Mac.
  * Startup auto-setup: detects OS / real CPU (Rosetta-proof) / GPU and, if
    RetroArch is missing, Intel-only on an M-chip Mac, or has no loadable
    N64 core, offers to install the right one. FreeBSD / OpenBSD / NetBSD use
    pkg / pkg_add / pkgin (no official BSD buildbot builds).
  * GPU detection (NVIDIA / AMD / Intel / Apple) orders the boot fallbacks:
    discrete NVIDIA/AMD try Vulkan + ParaLLEl early; Apple GPUs try OpenGL /
    software first. The dynarec is only dropped on Apple Silicon / ARM.
  * Linux/aarch64 and Windows x86 core downloads.

0.1.1.2
  * Crash fix: worker threads no longer call Tk directly (crashes / silent
    failures on non-threaded Tk builds, e.g. some macOS Pythons).
  * RetroArch / Mupen64Plus output is logged per game to ~/.catn64emu/logs/; a crash on
    ROM boot shows the exit code and the last log lines instead of nothing.
  * RetroArch quitting right after it opens: N64 cores can't render on the
    Metal (macOS default) / D3D video drivers, so each launch picks OpenGL
    core, or Vulkan if your N64 core is set to the ParaLLEl renderer.
  * "It asks for RetroArch" / Intel RetroArch + Apple Silicon core: cores are
    now chosen to match RetroArch's CPU type (an Intel RetroArch under Rosetta
    needs an x86_64 core). Download N64 Core fetches that CPU type, and a
    launch with no loadable core offers the download and then boots the game.
  * RetroArch found in ~/Applications, Steam, the App Store build (cores in
    Contents/Frameworks) and anywhere Spotlight knows; the Online Updater's
    core folder is read from retroarch.cfg. A native arm64 RetroArch is
    preferred over an Intel one.
  * A stale saved RetroArch path no longer blocks auto-detection.
  * "RetroArch not found" offers the download page instead of a dead end.
  * Apple Silicon: RetroArch is started with the same CPU type as the N64
    core (`arch -arm64`). An Intel/Rosetta Python otherwise launched RetroArch
    as Intel and the native core crashed it the moment the game booted.
    A core/RetroArch CPU mismatch is reported instead of crashing.
  * Crash on boot -> automatic retries: OpenGL + GLideN64 with the interpreter
    CPU (the dynarec JIT is the usual Apple Silicon crash), then Angrylion
    software video, then Vulkan + ParaLLEl. The mode that boots is
    remembered. Auto-detect Backend resets it.
  * Core download picks the real host CPU even under Rosetta.
  * Tools -> Diagnostics...: one copyable report (CPU types, RetroArch
    version, video driver, core options, last log lines).
  * Zipped games were all extracted as "game.z64", so every zipped game
    shared one save file / save-state slot. They keep their real name now.
  * Choosing RetroArch.app in Browse (macOS) now resolves to the real binary
    instead of failing as "not runnable".
  * "Start fullscreen" now applies to native Mupen64Plus too.
  * Closing the launcher while a game runs no longer deletes that game's
    extracted ROM / config folder.
  * Dialogs follow the dark theme; details pane resets when the list reloads.
  * A boot that fails with exit code 0 ("Failed to load content") is now
    reported too.
  * ROM hacks with a non-standard boot word are no longer rejected.
  * Each launch extracts ZIPs into its own folder (two launches of one ZIP
    no longer delete each other's ROM).
  * Scan requests made during a scan are queued instead of dropped.
  * Core download picks cores in priority order and no longer fails when the
    first listed archive is a different core than the one being checked.
  * Settings defaults are deep-copied (adding a folder no longer mutates them).

0.1.1.1
  * All buttons: black background, blue text (light, dark and system themes).
  * Buttons are ttk-styled so the colours also hold on macOS, where plain
    tk.Button ignores background colours.

0.1.1.a
  * Sidebar/toolbar buttons keep their own styling through theme passes.
  * Emulator and core paths expand "~" consistently.
  * Library scan runs off the main thread and validates ZIP contents.
  * Zip extractions get a per-launch directory, removed when the game exits.
  * Deterministic temp names (sha1 of path + mtime).
  * Encrypted / corrupt archives report a real message.
  * Non-macOS install guidance instead of a Homebrew-only hard stop.
"""
from __future__ import annotations
import html.parser
import io
import copy
import json
import os
import platform
import queue
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import urllib.parse
import urllib.request
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
from zipfile import ZipFile, BadZipFile

APP = 'CatN64Emu 0.1.1a'
CONFIG_DIR = Path.home() / '.catn64emu'
CONFIG_FILE = CONFIG_DIR / 'settings.json'
EXTS = {'.z64', '.n64', '.v64'}
ZIP_EXTS = EXTS | {'.zip'}
DEFAULTS = {'rom_dirs': [], 'emulator': '', 'core': '', 'extra_args': '',
            'geometry': '1120x740', 'controller_profile': 'Auto (RetroArch)',
            'fullscreen': False, 'theme': 'System'}
BUNDLE_DIR = Path(__file__).resolve().parent / 'catn64emu_runtime'
CORE_NAMES = ('mupen64plus_next_libretro', 'parallel_n64_libretro', 'mupen64plus_libretro')
CORE_EXTS = ('.dylib', '.so', '.dll')
TEMP_PREFIX = 'catn64emu_'
TEMP_MAX_AGE = 7 * 24 * 3600
LOG_DIR = CONFIG_DIR / 'logs'
BOOT_WINDOW = 20.0   # a non-zero exit sooner than this is a crash on boot

# Button palette — black buttons with blue text, independent of the theme.
BTN_BG = '#000000'
BTN_BG_ACTIVE = '#0d1626'
BTN_BG_PRESSED = '#16243a'
BTN_FG = '#3d9bff'
BTN_FG_ACTIVE = '#7cc0ff'
BTN_FG_DISABLED = '#2a4a70'
BTN_BORDER = '#1f3b5e'


# --------------------------------------------------------------------------- #
# settings / paths
# --------------------------------------------------------------------------- #
def expand(path) -> Path:
    """Expand ~ and return a Path, without touching the filesystem."""
    return Path(str(path)).expanduser()


def load_settings():
    try:
        obj = json.loads(CONFIG_FILE.read_text(encoding='utf-8'))
        base = copy.deepcopy(DEFAULTS)
        if isinstance(obj, dict):
            base.update(obj)
        if not isinstance(base.get('rom_dirs'), list):
            base['rom_dirs'] = []
        return base
    except (OSError, ValueError):
        return copy.deepcopy(DEFAULTS)


# --------------------------------------------------------------------------- #
# ROM header parsing
# --------------------------------------------------------------------------- #
def read_header(path, lenient=True):
    """Internal title of an N64 ROM. lenient accepts odd boot words (ROM hacks)."""
    try:
        with path.open('rb') as f:
            data = f.read(0x40)
        if len(data) < 0x40:
            return None
        magic = data[:4]
        if magic in (b'\x80\x37\x12\x40', b'\x80\x37\x12\x41'):
            raw = data
        elif magic == b'\x37\x80\x40\x12':
            raw = bytes(v for i in range(0, len(data) - 1, 2) for v in (data[i + 1], data[i]))
        elif magic == b'\x40\x12\x37\x80':
            raw = bytes(v for i in range(0, len(data) - 3, 4) for v in data[i:i + 4][::-1])
        elif lenient:
            raw = data            # hack/homebrew with a custom boot word: assume .z64
        else:
            return None
        name = raw[0x20:0x34].decode('ascii', 'replace').strip('\x00 ').strip()
        return name or path.stem
    except OSError:
        return None


def zip_has_rom(path):
    """Cheap pre-check so archives of documents never reach the library."""
    try:
        with ZipFile(path) as archive:
            return any(not i.is_dir() and Path(i.filename).suffix.lower() in EXTS
                       for i in archive.infolist())
    except (BadZipFile, OSError, RuntimeError):
        return False


# --------------------------------------------------------------------------- #
# backend discovery
# --------------------------------------------------------------------------- #
def _mdfind_apps():
    """RetroArch bundles anywhere on the Mac (Spotlight), incl. App Store / Steam copies."""
    if sys.platform != 'darwin' or not shutil.which('mdfind'):
        return []
    found = []
    for bid in ('com.libretro.RetroArch', 'com.libretro.dist.RetroArch',
                'com.libretro.RetroArchMetal'):
        try:
            r = subprocess.run(['mdfind', f"kMDItemCFBundleIdentifier == '{bid}'"],
                               capture_output=True, text=True, timeout=5)
            found += [Path(x) for x in r.stdout.splitlines() if x.endswith('.app')]
        except (OSError, subprocess.TimeoutExpired):
            pass
    return found


def emulator_candidates():
    apps = [BUNDLE_DIR / 'RetroArch.app', Path('/Applications/RetroArch.app'),
            Path.home() / 'Applications/RetroArch.app',
            Path.home() / 'Library/Application Support/Steam/steamapps/common/RetroArch/RetroArch.app',
            *_mdfind_apps()]
    out = [BUNDLE_DIR / 'retroarch', BUNDLE_DIR / 'retroarch.exe']
    rt = BUNDLE_DIR / 'RetroArch'                 # Tools → Install Native RetroArch (7z builds)
    if rt.is_dir():
        out += sorted(rt.rglob('retroarch.exe')) + sorted(rt.rglob('*.AppImage'))
    for app in apps:
        out.append(Path(normalize_exe(str(app))) if app.is_dir() else app / 'Contents/MacOS/RetroArch')
    which = shutil.which('retroarch')
    if which:
        out.append(Path(which))
    seen, uniq = set(), []
    for c in out:
        if c.is_file() and str(c) not in seen:
            seen.add(str(c))
            uniq.append(c)
    return uniq


def discover_emulator():
    """Private runtime, /Applications, ~/Applications, Steam, Spotlight, PATH.
    On Apple Silicon a native (arm64) RetroArch wins over an Intel-only one."""
    found = emulator_candidates()
    if sys.platform == 'darwin' and host_is_arm64():
        native = [c for c in found if 'arm64' in macho_archs(c)]
        if native:
            return str(native[0])
    return str(found[0]) if found else ''


def _libretro_dirs_from_cfg(exe):
    """libretro_directory from the user's retroarch.cfg (where the Online Updater saves cores)."""
    dirs = []
    for d in retroarch_config_dirs(exe):
        cfg = d / 'retroarch.cfg'
        try:
            for line in cfg.read_text(encoding='utf-8', errors='replace').splitlines():
                k, _, v = line.partition('=')
                if k.strip() == 'libretro_directory':
                    v = v.strip().strip('"')
                    if v.startswith(':'):              # ":/cores" = relative to RetroArch
                        v = str(expand(exe).parent / v.lstrip(':/')) if exe else ''
                    if v and v != 'default':
                        dirs.append(expand(v))
        except OSError:
            continue
    return dirs


def core_candidates(exe=''):
    roots = [*_libretro_dirs_from_cfg(exe)]
    if exe:
        e = expand(exe)
        roots += [e.parent / 'cores', e.parent.parent / 'Resources' / 'cores',
                  e.parent.parent.parent / 'Resources' / 'cores']
    roots += [BUNDLE_DIR / 'cores' / 'arm64', BUNDLE_DIR / 'cores' / 'x86_64', BUNDLE_DIR / 'cores',
              Path.home() / 'Library/Application Support/RetroArch/cores',
              Path.home() / 'Library/Containers/com.libretro.dist.RetroArch/Data/Library/'
                            'Application Support/RetroArch/cores',
              Path.home() / 'Library/Application Support/Steam/steamapps/common/RetroArch/cores',
              Path.home() / '.config/retroarch/cores',
              Path.home() / '.var/app/org.libretro.RetroArch/config/retroarch/cores',
              Path('/Applications/RetroArch.app/Contents/Resources/cores'),
              Path('/Applications/RetroArch.app/Contents/MacOS/cores'),
              Path('/usr/lib/libretro'), Path('/usr/lib/x86_64-linux-gnu/libretro'),
              Path('/usr/local/lib/libretro'), Path('/opt/homebrew/lib/libretro'),
              Path('/usr/pkg/lib/libretro'), Path('/usr/local/share/libretro/cores')]
    frameworks = []
    if exe and '.app/Contents/' in str(expand(exe)):
        # App Store builds ship cores inside the bundle as .framework packages.
        app_contents = Path(str(expand(exe)).split('.app/Contents/')[0] + '.app/Contents')
        frameworks.append(app_contents / 'Frameworks')
    out, seen = [], set()
    for name in CORE_NAMES:                       # priority: Mupen64Plus-Next first
        for root in roots:
            for ext in CORE_EXTS:
                p = root / (name + ext)
                if str(p) not in seen and p.is_file():
                    seen.add(str(p))
                    out.append(p)
        for fw in frameworks:
            p = fw / (name + '.framework') / name
            if str(p) not in seen and p.is_file():
                seen.add(str(p))
                out.append(p)
    return out


def core_matches(core, exe):
    """False only when both are Mach-O and share no CPU type (e.g. Intel RetroArch + arm64 core)."""
    if sys.platform != 'darwin' or not core or not exe:
        return True
    ra, co = macho_archs(expand(exe)), macho_archs(expand(core))
    return not ra or not co or bool(ra & co)


def discover_core(exe=''):
    """Find an N64 core RetroArch can actually load (matching CPU type first)."""
    found = core_candidates(exe)
    for c in found:
        if core_matches(c, exe):
            return str(c)
    return ''


def discover_standalone():
    """Native N64 fallback; does not need a libretro core."""
    paths = [BUNDLE_DIR / 'mupen64plus', Path('/opt/homebrew/bin/mupen64plus'),
             Path('/usr/local/bin/mupen64plus'), Path('/usr/bin/mupen64plus')]
    found = shutil.which('mupen64plus')
    if found:
        paths.insert(0, Path(found))
    return str(next((x for x in paths if x.is_file()), ''))


def resolve_core(configured, exe):
    """Honour the configured core if RetroArch can load it, else search."""
    candidate = expand(configured) if configured else None
    if candidate and candidate.is_file() and core_matches(candidate, exe):
        return str(candidate)
    return discover_core(exe)


def resolve_emulator(configured):
    """Configured RetroArch if it still exists and runs, else auto-detect."""
    exe = normalize_exe(configured.strip()) if configured else ''
    return exe if valid_retroarch(exe) else discover_emulator()


def normalize_exe(exe):
    """Map a macOS .app bundle to its binary (file pickers return the bundle)."""
    if not exe:
        return exe
    p = expand(exe)
    if p.suffix.lower() == '.app' and p.is_dir():
        macos = p / 'Contents' / 'MacOS'
        for cand in (macos / p.stem, macos / 'RetroArch', macos / 'mupen64plus'):
            if cand.is_file():
                return str(cand)
        found = sorted(x for x in macos.glob('*') if x.is_file()) if macos.is_dir() else []
        if found:
            return str(found[0])
    return str(exe)


def valid_retroarch(exe):
    """Accept anything runnable; the name check is a soft preference only."""
    if not exe:
        return False
    path = expand(exe)
    if path.is_file():
        return os.access(path, os.X_OK) or os.name == 'nt'
    return bool(shutil.which(exe))


def retroarch_core_available(exe, core):
    return valid_retroarch(exe) and bool(core) and expand(core).is_file()


# --------------------------------------------------------------------------- #
# core download
# --------------------------------------------------------------------------- #
class _Links(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []

    def handle_starttag(self, tag, attrs):
        if tag == 'a':
            url = dict(attrs).get('href', '')
            if url:
                self.links.append(url)


def _official_core_indexes(arch=None):
    """RetroArch's official buildbot; exact architecture matches only."""
    osname = platform.system()
    arch = (arch or platform.machine()).lower()
    if osname == 'Darwin':
        if arch not in ('arm64', 'x86_64'):
            arch = 'arm64' if host_is_arm64() else 'x86_64'   # not Rosetta Python's view
        return ['https://buildbot.libretro.com/nightly/apple/osx/arm64/latest/'] \
            if arch in ('arm64', 'aarch64') \
            else ['https://buildbot.libretro.com/nightly/apple/osx/x86_64/latest/']
    if osname == 'Windows':
        if arch in ('x86', 'i386', 'i686'):
            return ['https://buildbot.libretro.com/nightly/windows/x86/latest/']
        # x86_64, and ARM64 Windows (runs the x86_64 RetroArch + core emulated)
        return ['https://buildbot.libretro.com/nightly/windows/x86_64/latest/']
    if osname == 'Linux':
        if arch in ('x86_64', 'amd64'):
            return ['https://buildbot.libretro.com/nightly/linux/x86_64/latest/']
        if arch in ('aarch64', 'arm64'):
            return ['https://buildbot.libretro.com/nightly/linux/aarch64/latest/']
    return []


def _link_name(href):
    """Basename of an href, unquoted, without query string."""
    return urllib.parse.unquote(Path(href.split('?')[0]).name)


def target_core_arch(exe=''):
    """CPU type the core must have: RetroArch's (an Intel-only RetroArch under Rosetta
    needs an x86_64 core even on Apple Silicon), else the host's."""
    if sys.platform == 'darwin':
        ra = macho_archs(expand(exe)) if exe else set()
        if ra:
            return 'arm64' if 'arm64' in ra and host_is_arm64() else sorted(ra)[-1]
        return 'arm64' if host_is_arm64() else 'x86_64'
    return platform.machine().lower()


def download_n64_core(progress=lambda msg: None, arch=None):
    """Install an official libretro core built for `arch` (default: the host)."""
    indexes = _official_core_indexes(arch)
    core_dir = BUNDLE_DIR / 'cores' / (arch if sys.platform == 'darwin' and arch else '')
    if not indexes:
        raise RuntimeError('No official core download index configured for this OS/CPU architecture.')
    last = 'No compatible N64 core archive was listed.'
    limit = 90 * 1024 * 1024
    for base in indexes:
        progress('Checking official RetroArch buildbot...')
        try:
            with urllib.request.urlopen(
                    urllib.request.Request(base, headers={'User-Agent': 'CatN64Emu/0.1'}), timeout=20) as r:
                listing = r.read(2_000_000).decode('utf-8', 'replace')
            parser = _Links()
            parser.feed(listing)
            for name in CORE_NAMES:
                wanted = {name + s for s in ('.zip', '.dylib.zip', '.so.zip', '.dll.zip',
                                             '.dylib', '.so', '.dll')}
                matches = [u for u in parser.links if _link_name(u).lower() in wanted]
                if not matches:
                    continue
                href = matches[0]
                label = _link_name(href)
                url = urllib.parse.urljoin(base, href)
                progress('Downloading ' + label + '...')
                with urllib.request.urlopen(
                        urllib.request.Request(url, headers={'User-Agent': 'CatN64Emu/0.1'}), timeout=90) as r:
                    payload = r.read(limit + 1)
                if len(payload) > limit:
                    raise RuntimeError('Core download exceeds safety limit')
                if Path(label).suffix.lower() in CORE_EXTS:
                    dest = core_dir / label
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    tmp = dest.with_suffix(dest.suffix + '.partial')
                    tmp.write_bytes(payload)
                    tmp.replace(dest)
                    progress('N64 core installed: ' + dest.name)
                    return str(dest)
                with ZipFile(io.BytesIO(payload)) as z:
                    members = [m for m in z.infolist()
                               if Path(m.filename).name.startswith(name)
                               and Path(m.filename).suffix.lower() in CORE_EXTS
                               and m.file_size < limit]
                    if not members:
                        raise RuntimeError('Archive contains no recognized N64 libretro core')
                    member = members[0]
                    dest = core_dir / Path(member.filename).name
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    temp = dest.with_suffix(dest.suffix + '.partial')
                    with z.open(member) as src, temp.open('wb') as dst:
                        shutil.copyfileobj(src, dst)
                    temp.replace(dest)
                progress('N64 core installed: ' + dest.name)
                return str(dest)
        except Exception as e:
            last = str(e)
    raise RuntimeError('Could not install an official compatible N64 core. ' + last +
                       '\nSome platforms, including Apple Silicon, may not have a core available '
                       'on the official buildbot.')


# --------------------------------------------------------------------------- #
# RetroArch session config
# --------------------------------------------------------------------------- #
def retroarch_config_dirs(exe=''):
    """Places RetroArch keeps retroarch.cfg / core options on each OS."""
    dirs = [Path.home() / 'Library/Application Support/RetroArch',
            Path.home() / '.config/retroarch',
            Path.home() / '.var/app/org.libretro.RetroArch/config/retroarch']
    if os.environ.get('APPDATA'):
        dirs.append(Path(os.environ['APPDATA']) / 'RetroArch')
    if exe:
        dirs.insert(0, expand(exe).parent)       # portable / Windows installs
    return dirs


def user_core_option(exe, key):
    """Value the user saved for a core option, or '' (checks per-core + global files)."""
    for d in retroarch_config_dirs(exe):
        for f in (d / 'config/Mupen64Plus-Next/Mupen64Plus-Next.opt',
                  d / 'config/ParaLLEl N64/ParaLLEl N64.opt',
                  d / 'retroarch-core-options.cfg'):
            try:
                for line in f.read_text(encoding='utf-8', errors='replace').splitlines():
                    k, _, v = line.partition('=')
                    if k.strip() == key:
                        return v.strip().strip('"')
            except OSError:
                continue
    return ''


def n64_video_driver(core_path, exe=''):
    """A video driver the N64 core can actually render with.

    RetroArch for macOS defaults to Metal (Windows builds may default to D3D),
    but the N64 cores only render through OpenGL or Vulkan: under Metal the core
    loads, the game fails to start, the menu flashes and RetroArch quits.
    """
    name = Path(core_path).name.lower()
    if name.startswith('mupen64plus_next'):
        rdp = user_core_option(exe, 'mupen64plus-rdp-plugin')
        return 'vulkan' if rdp == 'parallel' else 'glcore'
    if name.startswith('parallel_n64'):
        gfx = user_core_option(exe, 'parallel-n64-gfxplugin')
        return 'vulkan' if gfx == 'parallel' else 'gl'
    return 'gl'                                   # legacy mupen64plus_libretro


def merge_appendconfig(args, cfg_path):
    """Add our appendconfig, joining any the user passed (RetroArch uses '|')."""
    out, merged, i = [], False, 0
    while i < len(args):
        a = args[i]
        if a == '--appendconfig' and i + 1 < len(args):
            out += [a, args[i + 1] + '|' + cfg_path]
            merged, i = True, i + 2
            continue
        if a.startswith('--appendconfig='):
            a, merged = a + '|' + cfg_path, True
        out.append(a)
        i += 1
    return out if merged else out + ['--appendconfig', cfg_path]


# --------------------------------------------------------------------------- #
# CPU type matching (Apple Silicon) + safe-mode boot stages
# --------------------------------------------------------------------------- #
_MACHO_CPU = {0x01000007: 'x86_64', 0x0100000C: 'arm64'}


def macho_archs(path):
    """CPU types in a Mach-O binary/dylib (empty set if not Mach-O, e.g. Linux/Windows)."""
    try:
        with open(path, 'rb') as f:
            head = f.read(4096)
    except OSError:
        return set()
    if len(head) < 8:
        return set()
    magic_be = int.from_bytes(head[:4], 'big')
    if magic_be in (0xCAFEBABE, 0xCAFEBABF):              # universal ("fat") binary
        count = int.from_bytes(head[4:8], 'big')
        size = 20 if magic_be == 0xCAFEBABE else 32
        archs = set()
        for i in range(min(count, 16)):
            off = 8 + i * size
            cpu = int.from_bytes(head[off:off + 4], 'big')
            if cpu in _MACHO_CPU:
                archs.add(_MACHO_CPU[cpu])
        return archs
    if int.from_bytes(head[:4], 'little') == 0xFEEDFACF:  # thin 64-bit
        cpu = int.from_bytes(head[4:8], 'little')
        return {_MACHO_CPU[cpu]} if cpu in _MACHO_CPU else set()
    return set()


def host_is_arm64():
    """True on Apple Silicon even when this Python itself runs under Rosetta."""
    if sys.platform != 'darwin':
        return platform.machine().lower() in ('arm64', 'aarch64')
    try:
        r = subprocess.run(['sysctl', '-n', 'hw.optional.arm64'], capture_output=True,
                           text=True, timeout=2)
        return r.stdout.strip() == '1'
    except (OSError, subprocess.TimeoutExpired):
        return platform.machine().lower() == 'arm64'


def arch_prefix(exe, core):
    """(['arch', '-arm64'] or [], error). An Intel (Rosetta) Python would otherwise
    start RetroArch as Intel too, and a native Apple Silicon core then can't load —
    RetroArch dies the moment the game boots."""
    if sys.platform != 'darwin':
        return [], ''
    ra, co = macho_archs(expand(exe)), macho_archs(expand(core))
    if not ra or not co:
        return [], ''
    common = ra & co
    if not common:
        return [], (f'The N64 core is built for {"/".join(sorted(co))} but RetroArch is '
                    f'{"/".join(sorted(ra))}, so RetroArch would crash on boot.\n\n'
                    'In RetroArch use Online Updater → Core Downloader → Nintendo - Nintendo 64 '
                    '(Mupen64Plus-Next), then Tools → Auto-detect Backend here.')
    want = 'arm64' if host_is_arm64() and 'arm64' in common else sorted(common)[0]
    return (['arch', '-' + want] if shutil.which('arch') else []), ''


def _apple_or_arm():
    return (sys.platform == 'darwin' and host_is_arm64()) or \
        platform.machine().lower() in ('arm64', 'aarch64')


def build_stages():
    """Boot fallbacks: (label, rdp, video_driver, cpu). Stage 0 = user's own settings."""
    interp = 'cached_interpreter' if _apple_or_arm() else 'dynamic_recompiler'
    cpu_note = 'interpreter CPU (no dynarec JIT)' if interp == 'cached_interpreter' else 'dynarec CPU'
    gl = ('OpenGL + GLideN64, ' + cpu_note, 'gliden64', 'glcore', interp)
    vk = ('Vulkan + ParaLLEl, ' + cpu_note, 'parallel', 'vulkan', interp)
    sw = ('OpenGL + Angrylion software video, interpreter CPU', 'angrylion', 'glcore',
          'cached_interpreter')
    safe = ('OpenGL + GLideN64, interpreter CPU', 'gliden64', 'glcore', 'cached_interpreter')
    vendor = gpu_info()[0] if 'gpu_info' in globals() else 'Unknown'
    if vendor in ('NVIDIA', 'AMD'):
        order = [vk, gl, safe, sw]                 # strong Vulkan drivers
    elif vendor == 'Apple':
        order = [gl, sw, vk]                       # MoltenVK last
    else:
        order = [gl, vk, safe, sw]
    seen, stages = set(), [('your RetroArch settings + an N64-capable video driver', '', '', '')]
    for st in order:
        if st[1:] not in seen:
            seen.add(st[1:])
            stages.append(st)
    return stages


_STAGES = None


def stages():
    global _STAGES
    if _STAGES is None:
        _STAGES = build_stages()
    return _STAGES


class _StageLabels:
    """SAFE_STAGES[i] / len(SAFE_STAGES) keep working for the UI code."""
    def __getitem__(self, i):
        return stages()[i][0]

    def __len__(self):
        return len(stages())


SAFE_STAGES = _StageLabels()


def stage_session(core_path, exe, stage):
    """(retroarch cfg overrides, core options) for a boot attempt.

    Stage 0 changes only the video driver and lets RetroArch save normally.
    Later stages use a temporary core-options file (and don't save RetroArch's
    config on exit, so those temporary paths never end up in retroarch.cfg).
    """
    if stage == 0:
        return {'video_driver': n64_video_driver(core_path, exe)}, {}
    _, rdp, driver, cpu = stages()[stage]
    name = Path(core_path).name.lower()
    cfg = {'video_driver': driver, 'config_save_on_exit': 'false'}
    if name.startswith('mupen64plus_next'):
        opts = {'mupen64plus-rdp-plugin': rdp, 'mupen64plus-rsp-plugin': 'hle',
                'mupen64plus-cpucore': cpu}
    elif name.startswith('parallel_n64'):
        opts = {'parallel-n64-gfxplugin': 'glide64' if rdp == 'gliden64' else rdp,
                'parallel-n64-rspplugin': 'auto', 'parallel-n64-cpucore': cpu}
        if driver == 'glcore':
            cfg['video_driver'] = 'gl'
    else:
        opts, cfg['video_driver'] = {}, 'gl'
    return cfg, opts


BOOT_FAIL_MARKERS = ('failed to load content', 'failed to open libretro core',
                     'failed to initialize', 'failed to init video', 'could not create',
                     'failed to create')


# --------------------------------------------------------------------------- #
# native RetroArch provisioning (every OS / CPU)
# --------------------------------------------------------------------------- #
BUILDBOT = 'https://buildbot.libretro.com'
STABLE_FALLBACK = '1.22.2'
UA = {'User-Agent': 'CatN64Emu/0.1.1a'}


def retroarch_package():
    """(url_candidates, kind, label) of the official build for this machine."""
    osname, arch = platform.system(), platform.machine().lower()
    ver = _STABLE or STABLE_FALLBACK              # no network on the UI thread
    if osname == 'Darwin':
        # Universal binary: native on Apple M-series and on Intel Macs.
        return ([f'{BUILDBOT}/stable/{ver}/apple/osx/universal/RetroArch_Metal.dmg',
                 f'{BUILDBOT}/nightly/apple/osx/universal/RetroArch_Metal.dmg'],
                'dmg', f'RetroArch {ver} Universal (Apple Silicon + Intel)')
    if osname == 'Windows':
        sub = 'x86' if arch in ('x86', 'i386', 'i686') else 'x86_64'
        return ([f'{BUILDBOT}/stable/{ver}/windows/{sub}/RetroArch.7z',
                 f'{BUILDBOT}/nightly/windows/{sub}/RetroArch.7z'],
                '7z', f'RetroArch {ver} Windows {sub}' +
                (' (via ARM64 emulation)' if arch in ('arm64', 'aarch64') else ''))
    if osname == 'Linux':
        if arch in ('x86_64', 'amd64'):
            return ([f'{BUILDBOT}/stable/{ver}/linux/x86_64/RetroArch.7z',
                     f'{BUILDBOT}/nightly/linux/x86_64/RetroArch.7z'],
                    '7z', f'RetroArch {ver} Linux x86_64 (AppImage)')
        if arch in ('aarch64', 'arm64'):
            return ([f'{BUILDBOT}/nightly/linux/aarch64/RetroArch.7z'],
                    '7z', 'RetroArch nightly Linux aarch64')
    if is_bsd():
        return [], 'bsd-pkg', f'RetroArch from the {osname} package manager'
    return [], '', f'{osname} {arch}'


_STABLE = None


def latest_stable_version():
    global _STABLE
    if _STABLE:
        return _STABLE
    try:
        with urllib.request.urlopen(urllib.request.Request(BUILDBOT + '/stable/', headers=UA),
                                    timeout=15) as r:
            parser = _Links()
            parser.feed(r.read(500_000).decode('utf-8', 'replace'))
        vers = []
        for href in parser.links:
            name = _link_name(href.rstrip('/'))
            parts = name.split('.')
            if len(parts) >= 2 and all(p.isdigit() for p in parts):
                vers.append(tuple(int(p) for p in parts))
        _STABLE = '.'.join(map(str, max(vers))) if vers else STABLE_FALLBACK
    except Exception:
        _STABLE = STABLE_FALLBACK
    return _STABLE


def download_file(url, dest, progress, limit=900 * 1024 * 1024):
    """Stream a download to dest with percentage progress."""
    tmp = dest.with_name(dest.name + '.partial')
    with urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=60) as r:
        total = int(r.headers.get('Content-Length') or 0)
        done, last = 0, -1
        with tmp.open('wb') as f:
            while True:
                chunk = r.read(1 << 20)
                if not chunk:
                    break
                done += len(chunk)
                if done > limit:
                    raise RuntimeError('Download exceeds safety limit')
                f.write(chunk)
                pct = int(done * 100 / total) if total else -1
                if pct != last and (pct % 5 == 0 or pct < 0):
                    last = pct
                    progress(f'Downloading {dest.name}: ' +
                             (f'{pct}%' if pct >= 0 else f'{done // (1 << 20)} MB'))
    if total and done < total:
        raise RuntimeError('Download was cut off; try again.')
    tmp.replace(dest)
    return dest


def extract_7z(archive, dest, progress):
    """py7zr if installed, else 7z/7za/7zz, else bsdtar/tar (Windows 10+ tar.exe reads 7z)."""
    dest.mkdir(parents=True, exist_ok=True)
    lib = BUNDLE_DIR / 'pylib'
    if lib.is_dir() and str(lib) not in sys.path:   # installed by an earlier run
        sys.path.insert(0, str(lib))
    try:
        import py7zr                                # optional dependency
        with py7zr.SevenZipFile(archive, 'r') as z:
            z.extractall(dest)
        return
    except ImportError:
        pass
    tried = []
    for cmd in (['7z', 'x', '-y', f'-o{dest}', str(archive)],
                ['7za', 'x', '-y', f'-o{dest}', str(archive)],
                ['7zz', 'x', '-y', f'-o{dest}', str(archive)],
                ['bsdtar', '-xf', str(archive), '-C', str(dest)],
                ['tar', '-xf', str(archive), '-C', str(dest)]):
        tool = shutil.which(cmd[0])
        if not tool:
            continue
        progress(f'Extracting with {cmd[0]}…')
        r = subprocess.run([tool, *cmd[1:]], capture_output=True, text=True, timeout=900)
        if r.returncode == 0 and any(dest.iterdir()):
            return
        tried.append(cmd[0])
    # Private library folder: importable immediately (a fresh --user site is not on
    # sys.path until restart) and allowed on PEP 668 "externally managed" Pythons.
    lib = BUNDLE_DIR / 'pylib'
    progress('Installing py7zr (7-Zip support) into catn64emu_runtime/pylib…')
    r = None
    for extra in ([], ['--break-system-packages']):
        r = subprocess.run([sys.executable, '-m', 'pip', 'install', '--quiet', '--upgrade',
                            '--target', str(lib), *extra, 'py7zr'],
                           capture_output=True, text=True, timeout=900)
        if r.returncode == 0:
            break
    if r is not None and r.returncode == 0:
        import importlib
        if str(lib) not in sys.path:
            sys.path.insert(0, str(lib))
        importlib.invalidate_caches()
        import py7zr
        with py7zr.SevenZipFile(archive, 'r') as z:
            z.extractall(dest)
        return
    raise RuntimeError('Could not extract the RetroArch .7z archive (tried '
                       f'{", ".join(tried) or "no 7z tools"} and pip install py7zr). '
                       'Install 7-Zip, then retry.')


def _install_dmg(dmg, progress):
    mnt = Path(tempfile.mkdtemp(prefix='catn64emu_dmg_'))
    progress('Opening RetroArch disk image…')
    r = subprocess.run(['hdiutil', 'attach', '-nobrowse', '-readonly', '-noautoopen',
                        '-mountpoint', str(mnt), str(dmg)],
                       input='Y\n', capture_output=True, text=True, timeout=300)
    if r.returncode:
        raise RuntimeError('hdiutil could not open the disk image: ' + (r.stderr or r.stdout)[-400:])
    try:
        apps = sorted(mnt.glob('*.app'))
        if not apps:
            raise RuntimeError('No RetroArch.app inside the disk image.')
        dest = BUNDLE_DIR / 'RetroArch.app'
        if dest.exists():
            shutil.rmtree(dest, ignore_errors=True)
        BUNDLE_DIR.mkdir(parents=True, exist_ok=True)
        progress('Copying RetroArch.app…')
        r = subprocess.run(['ditto', str(apps[0]), str(dest)], capture_output=True, text=True,
                           timeout=600)
        if r.returncode:
            raise RuntimeError('Copy failed: ' + r.stderr[-400:])
        subprocess.run(['xattr', '-dr', 'com.apple.quarantine', str(dest)],
                       capture_output=True, timeout=60)
    finally:
        subprocess.run(['hdiutil', 'detach', '-quiet', str(mnt)], capture_output=True, timeout=120)
        shutil.rmtree(mnt, ignore_errors=True)
    return Path(normalize_exe(str(dest)))


def _find_installed_binary(root):
    if sys.platform.startswith('win'):
        hits = sorted(root.rglob('retroarch.exe'))
    else:
        hits = sorted(root.rglob('*.AppImage')) or \
            [p for p in sorted(root.rglob('retroarch')) if p.is_file()]
    if not hits:
        raise RuntimeError('The RetroArch archive did not contain a RetroArch program.')
    exe = hits[0]
    if not sys.platform.startswith('win'):
        exe.chmod(exe.stat().st_mode | 0o111)
    return exe


def install_flatpak_retroarch(progress):
    """Linux fallback: Flathub RetroArch behind a small wrapper script."""
    flatpak = shutil.which('flatpak')
    if not flatpak:
        raise RuntimeError('No RetroArch build for this CPU and Flatpak is not installed.')
    progress('Installing RetroArch from Flathub…')
    subprocess.run([flatpak, 'remote-add', '--user', '--if-not-exists', 'flathub',
                    'https://dl.flathub.org/repo/flathub.flatpakrepo'], capture_output=True)
    r = subprocess.run([flatpak, 'install', '--user', '-y', 'flathub', 'org.libretro.RetroArch'],
                       capture_output=True, text=True, timeout=1800)
    if r.returncode:
        raise RuntimeError('Flatpak install failed: ' + (r.stderr or r.stdout)[-600:])
    BUNDLE_DIR.mkdir(parents=True, exist_ok=True)
    wrapper = BUNDLE_DIR / 'retroarch'
    wrapper.write_text('#!/bin/sh\nexec flatpak run --filesystem=home --filesystem=/tmp '
                       'org.libretro.RetroArch "$@"\n', encoding='utf-8')
    wrapper.chmod(0o755)
    return wrapper


def host_summary():
    """Human-readable OS / CPU (real CPU even under Rosetta) for dialogs + diagnostics."""
    osname = platform.system()
    if osname == 'Darwin':
        cpu = 'Apple M-series (arm64)' if host_is_arm64() else 'Intel (x86_64)'
        return f'macOS {platform.mac_ver()[0]} on {cpu}'
    if osname == 'Windows':
        return f'Windows {platform.release()} on {platform.machine()}'
    return f'{osname} {platform.release()} on {platform.machine()}'


def is_bsd():
    return 'bsd' in platform.system().lower() or platform.system() == 'DragonFly'


def install_bsd_retroarch(progress):
    """BSDs have no official buildbot builds: use the system package manager."""
    osname = platform.system()
    root = [] if os.geteuid() == 0 else \
        (['sudo'] if shutil.which('sudo') else ['doas'] if shutil.which('doas') else None)
    if root is None:
        raise RuntimeError('Installing RetroArch needs root: run  pkg install retroarch  '
                           '(or your BSD\'s equivalent) as root, then Tools → Auto-detect.')
    if osname in ('FreeBSD', 'DragonFly'):
        cmds = [[*root, 'pkg', 'install', '-y', 'retroarch'],
                [*root, 'pkg', 'install', '-y', 'libretro-mupen64plus']]
    elif osname == 'OpenBSD':
        cmds = [[*root, 'pkg_add', '-I', 'retroarch']]
    elif osname == 'NetBSD':
        cmds = [[*root, 'pkgin', '-y', 'install', 'retroarch']]
    else:
        raise RuntimeError(f'Unknown BSD ({osname}); install RetroArch with its package manager.')
    for i, cmd in enumerate(cmds):
        progress('Running: ' + ' '.join(cmd))
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=1800,
                           stdin=subprocess.DEVNULL)
        if r.returncode and i == 0:              # RetroArch itself is required; cores optional
            raise RuntimeError(' '.join(cmd) + ' failed:\n' + (r.stderr or r.stdout)[-600:])
    exe = shutil.which('retroarch')
    if not exe:
        raise RuntimeError('The package installed but no retroarch command was found.')
    return Path(exe)


def install_native_retroarch(progress=lambda m: None):
    """Download + install the official RetroArch for this OS/CPU. Returns the binary."""
    if is_bsd():
        return install_bsd_retroarch(progress)
    latest_stable_version()                       # resolve newest stable (worker thread)
    urls, kind, label = retroarch_package()
    if not urls:
        if platform.system() == 'Linux':
            return install_flatpak_retroarch(progress)
        raise RuntimeError(f'No official RetroArch build is published for {label}.')
    BUNDLE_DIR.mkdir(parents=True, exist_ok=True)
    dl = Path(tempfile.mkdtemp(prefix='catn64emu_dl_'))
    try:
        last = ''
        for url in urls:
            try:
                progress(f'Downloading {label}…')
                pkg = download_file(url, dl / _link_name(url), progress)
                break
            except Exception as exc:                 # try the next mirror / nightly
                last = str(exc)
        else:
            if platform.system() == 'Linux':
                return install_flatpak_retroarch(progress)
            raise RuntimeError(f'Could not download {label}: {last}')
        if kind == 'dmg':
            return _install_dmg(pkg, progress)
        target = BUNDLE_DIR / 'RetroArch'
        if target.exists():
            shutil.rmtree(target, ignore_errors=True)
        extract_7z(pkg, target, progress)
        return _find_installed_binary(target)
    finally:
        shutil.rmtree(dl, ignore_errors=True)


# --------------------------------------------------------------------------- #
# GPU detection
# --------------------------------------------------------------------------- #
_GPU = None
_PCI_VENDORS = {'0x10de': 'NVIDIA', '0x1002': 'AMD', '0x1022': 'AMD', '0x8086': 'Intel'}


def gpu_info():
    """(vendor, description). vendor: NVIDIA / AMD / Intel / Apple / Unknown."""
    global _GPU
    if _GPU:
        return _GPU
    desc = ''
    try:
        if sys.platform == 'darwin':
            r = subprocess.run(['system_profiler', 'SPDisplaysDataType'], capture_output=True,
                               text=True, timeout=15)
            desc = ' / '.join(l.split(':', 1)[1].strip() for l in r.stdout.splitlines()
                              if 'Chipset Model' in l)
        elif sys.platform.startswith('win'):
            r = subprocess.run(['powershell', '-NoProfile', '-Command',
                                '(Get-CimInstance Win32_VideoController).Name'],
                               capture_output=True, text=True, timeout=20)
            desc = ' / '.join(x.strip() for x in r.stdout.splitlines() if x.strip())
        else:
            names = []
            for card in sorted(Path('/sys/class/drm').glob('card[0-9]')):
                try:
                    vid = (card / 'device' / 'vendor').read_text().strip()
                    names.append(_PCI_VENDORS.get(vid, vid))
                except OSError:
                    pass
            desc = ' / '.join(names)
            if shutil.which('lspci'):
                r = subprocess.run(['lspci'], capture_output=True, text=True, timeout=10)
                vga = [l.split(': ', 1)[-1] for l in r.stdout.splitlines()
                       if 'VGA' in l or '3D controller' in l]
                desc = ' / '.join(vga) or desc
    except (OSError, subprocess.TimeoutExpired):
        pass
    low = desc.lower()
    vendor = ('NVIDIA' if 'nvidia' in low or 'geforce' in low or 'rtx' in low else
              'AMD' if 'amd' in low or 'radeon' in low else
              'Apple' if 'apple' in low or (sys.platform == 'darwin' and host_is_arm64()) else
              'Intel' if 'intel' in low or 'arc' in low else 'Unknown')
    _GPU = (vendor, desc or 'unknown')
    return _GPU


# --------------------------------------------------------------------------- #
# GUI
# --------------------------------------------------------------------------- #
class Launcher(tk.Tk):
    def __init__(self):
        super().__init__()
        self.cfg = load_settings()
        self.title(APP + '  |  AC Kondo Solutions')
        self.geometry(self.cfg.get('geometry') or DEFAULTS['geometry'])
        self.minsize(760, 480)
        self.emulator = tk.StringVar(value=self.cfg.get('emulator') or discover_emulator())
        self.extra_args = tk.StringVar(value=self.cfg.get('extra_args', ''))
        # Core discovery touches a dozen directories; defer it past first paint.
        self.core = tk.StringVar(value=self.cfg.get('core', ''))
        self.controller_profile = tk.StringVar(value=self.cfg.get('controller_profile', 'Auto (RetroArch)'))
        self.fullscreen = tk.BooleanVar(value=self.cfg.get('fullscreen', False))
        self.theme_choice = tk.StringVar(value=self.cfg.get('theme', 'System'))
        self.search = tk.StringVar()
        self.search.trace_add('write', lambda *_: self.populate())
        self.games = []
        self.visible = {}
        self._btn_role = {}
        self._scanning = False
        self._rescan = False
        self._running = 0                       # emulator processes still open
        self.tempdir = Path(tempfile.mkdtemp(prefix=TEMP_PREFIX))
        # Worker threads never touch Tk; they queue callables for the main loop.
        self._ui_queue = queue.Queue()
        threading.Thread(target=gpu_info, daemon=True).start()   # warm cache off the UI thread
        self.after(30, self._drain_ui_queue)
        self._make_ui()
        self.apply_theme()
        self.scan()
        self.after(60, self._deferred_core_detect)
        self.after(900, self._startup_setup_check)
        self.protocol('WM_DELETE_WINDOW', self.close)

    def _ui(self, fn):
        """Thread-safe: run fn() on the Tk main thread."""
        self._ui_queue.put(fn)

    def _drain_ui_queue(self):
        try:
            while True:
                fn = self._ui_queue.get_nowait()
                try:
                    fn()
                except Exception as exc:       # one bad callback must not kill the app
                    self.status.set(f'Internal error: {exc}')
        except queue.Empty:
            pass
        try:
            self.after(30, self._drain_ui_queue)
        except tk.TclError:
            pass

    def backend_state(self):
        """('ok' | 'no_retroarch' | 'intel_on_m' | 'no_core', exe, core)."""
        exe = resolve_emulator(self.emulator.get())
        core = resolve_core(self.core.get().strip(), exe) if exe else ''
        if not valid_retroarch(exe):
            return ('ok' if discover_standalone() else 'no_retroarch'), exe, core
        if sys.platform == 'darwin' and host_is_arm64() and macho_archs(expand(exe)) \
                and 'arm64' not in macho_archs(expand(exe)):
            return 'intel_on_m', exe, core
        return ('ok' if core else 'no_core'), exe, core

    def _startup_setup_check(self):
        """Auto-detect OS/CPU/GPU on start; offer the matching native backend once."""
        state, exe, core = self.backend_state()
        if exe and exe != self.emulator.get().strip():
            self.emulator.set(exe)
        if core and core != self.core.get().strip():
            self.core.set(core)
        if state == 'ok' or self.cfg.get('setup_declined') == state:
            self.status.set(f'Ready  •  {host_summary()}  •  GPU: {gpu_info()[0]}'
                            + ('' if state == 'ok' else '  •  backend setup skipped'))
            return
        label = retroarch_package()[2]
        why = {'no_retroarch': 'RetroArch is not installed.',
               'intel_on_m': f'The RetroArch found is Intel-only and runs through Rosetta on '
                             f'this M-chip Mac, so it cannot load native cores:\n{exe}',
               'no_core': f'RetroArch was found but has no N64 core it can load:\n{exe}'}[state]
        what = (f'download the matching N64 core ({target_core_arch(exe)})' if state == 'no_core'
                else f'install {label} into the catn64emu_runtime folder, plus a matching '
                     'N64 core')
        if messagebox.askyesno('Set up the N64 backend?',
                               f'Detected: {host_summary()}\nGPU: {gpu_info()[0]} '
                               f'({gpu_info()[1]})\n\n{why}\n\nCatN64Emu can {what} now.\n\n'
                               'Set it up now? (No = don\'t ask again for this.)'):
            self.cfg.pop('setup_declined', None)
            if state == 'no_core':
                self.install_core(arch=target_core_arch(exe))
            else:
                self.install_retroarch()
        else:
            self.cfg['setup_declined'] = state
            self.save()

    def _deferred_core_detect(self):
        if not self.core.get().strip():
            found = discover_core(self.emulator.get())
            if found:
                self.core.set(found)

    # ---------------------------------------------------------------- layout
    def _make_ui(self):
        """Parallel Launcher-inspired three-pane library with launch and controller tools."""
        panel, navy = '#ffffff', '#142e52'
        style = ttk.Style(self)
        if 'clam' in style.theme_names():
            style.theme_use('clam')
        style.configure('Treeview', font=('Arial', 11), rowheight=32,
                        background='white', fieldbackground='white')
        style.configure('Treeview.Heading', font=('Arial', 10, 'bold'))
        style.map('Treeview', background=[('selected', '#d8e8ff')],
                  foreground=[('selected', '#102a50')])

        menu = tk.Menu(self)
        filemenu = tk.Menu(menu, tearoff=False)
        for label, fn in [('Add ROM Folder…', self.add_folder), ('Open ROM…', self.open_file),
                          ('Refresh Library', self.scan)]:
            filemenu.add_command(label=label, command=fn)
        filemenu.add_separator()
        filemenu.add_command(label='Exit', command=self.close)
        menu.add_cascade(label='File', menu=filemenu)
        self.file_menu = filemenu

        tools = tk.Menu(menu, tearoff=False)
        tools.add_command(label='RetroArch / Emulator Settings…', command=self.configure_emulator)
        tools.add_command(label='Auto-detect Backend', command=self.autodetect)
        tools.add_command(label='Install Native RetroArch (this computer)…',
                          command=self.install_retroarch)
        tools.add_command(label='Download N64 Core', command=self.install_core)
        tools.add_command(label='Install Native Backend', command=self.install_native_backend)
        tools.add_command(label='Controller Setup…', command=self.controller_setup)
        tools.add_separator()
        tools.add_command(label='Diagnostics…', command=self.diagnostics)
        menu.add_cascade(label='Tools', menu=tools)
        self.tools_menu = tools

        appearance = tk.Menu(menu, tearoff=False)
        for choice in ('Light', 'Dark', 'System'):
            appearance.add_radiobutton(label=choice, variable=self.theme_choice,
                                       value=choice, command=self.change_theme)
        menu.add_cascade(label='Appearance', menu=appearance)
        self.appearance_menu = appearance
        self.menu_bar = menu

        helpmenu = tk.Menu(menu, tearoff=False)
        helpmenu.add_command(label='About', command=lambda: messagebox.showinfo(APP,
            APP + ' — Python N64 launcher\n© AC Kondo 1999–2026\n\n'
            'Parallel Launcher-inspired layout. Independent project, not an official port.\n'
            'Uses RetroArch/libretro or native Mupen64Plus.'))
        menu.add_cascade(label='Help', menu=helpmenu)
        self.help_menu = helpmenu
        self.config(menu=menu)

        header = tk.Frame(self, bg=navy, padx=22, pady=16)
        header.pack(fill='x')
        self.header_frame = header
        tk.Label(header, text='CATN64EMU 0.1.1A', font=('Arial', 25, 'bold'),
                 fg='white', bg=navy).pack(side='left')
        tk.Label(header, text='N64 GAME LIBRARY  •  AC KONDO SOLUTIONS',
                 font=('Arial', 10, 'bold'), fg='#b8d9ff', bg=navy).pack(side='right')

        toolbar = tk.Frame(self, bg='#dfe9f5', padx=14, pady=10)
        toolbar.pack(fill='x')
        self.toolbar_frame = toolbar
        for text, cmd in [('＋ Add Games', self.add_folder), ('Open ROM', self.open_file),
                          ('↻ Refresh', self.scan), ('🎮 Controllers', self.controller_setup)]:
            btn = ttk.Button(toolbar, text=text, command=cmd, style='Toolbar.TButton',
                             cursor='hand2')
            btn.pack(side='left', padx=(0, 7))
            self._btn_role[btn] = 'toolbar'
        tk.Label(toolbar, text='Search', bg='#dfe9f5').pack(side='left', padx=(16, 6))
        ttk.Entry(toolbar, textvariable=self.search).pack(side='left', fill='x', expand=True)

        body = tk.PanedWindow(self, orient='horizontal', bg='#edf2f8', sashwidth=5, bd=0)
        body.pack(fill='both', expand=True, padx=12, pady=12)
        self.body_frame = body

        sidebar = tk.Frame(body, bg=panel, width=195,
                           highlightbackground='#ccd9e9', highlightthickness=1)
        body.add(sidebar, minsize=160)
        tk.Label(sidebar, text='LIBRARY', bg=panel, fg=navy,
                 font=('Arial', 12, 'bold'), padx=15, pady=16).pack(anchor='w')
        for title, cmd in [('All Games', self.scan), ('Add ROM Folder', self.add_folder),
                           ('Emulator Settings', self.configure_emulator),
                           ('Controller Setup', self.controller_setup)]:
            btn = ttk.Button(sidebar, text=title, command=cmd, style='Sidebar.TButton',
                             cursor='hand2')
            btn.pack(fill='x', padx=8, pady=2)
            self._btn_role[btn] = 'sidebar'

        center = tk.Frame(body, bg=panel, highlightbackground='#ccd9e9', highlightthickness=1)
        body.add(center, minsize=380)
        tk.Label(center, text='YOUR GAMES', bg=panel, fg=navy,
                 font=('Arial', 12, 'bold'), padx=15, pady=13).pack(anchor='w')
        listbox = tk.Frame(center, bg=panel)
        listbox.pack(fill='both', expand=True, padx=10, pady=(0, 10))
        self.tree = ttk.Treeview(listbox, columns=('game', 'type', 'location'),
                                 show='headings', selectmode='browse')
        for key, name, width, stretch in [('game', 'Game', 260, True),
                                          ('type', 'Format', 75, False),
                                          ('location', 'Location', 260, True)]:
            self.tree.heading(key, text=name)
            self.tree.column(key, width=width, stretch=stretch)
        scroll = ttk.Scrollbar(listbox, orient='vertical', command=self.tree.yview)
        self.tree.configure(yscrollcommand=scroll.set)
        self.tree.pack(side='left', fill='both', expand=True)
        scroll.pack(side='right', fill='y')
        self.tree.bind('<Double-1>', lambda _: self.launch_selected())
        self.tree.bind('<Return>', lambda _: self.launch_selected())
        self.tree.bind('<<TreeviewSelect>>', lambda _: self.update_details())

        details = tk.Frame(body, bg=panel, width=255,
                           highlightbackground='#ccd9e9', highlightthickness=1)
        body.add(details, minsize=210)
        tk.Label(details, text='GAME DETAILS', bg=panel, fg=navy,
                 font=('Arial', 12, 'bold'), pady=16).pack()
        self.detail = tk.StringVar(value='Select a ROM to view details.')
        tk.Label(details, textvariable=self.detail, wraplength=225, justify='left',
                 bg=panel, fg='#3b526e', padx=12, pady=20).pack(fill='x')
        tk.Label(details, text='Controller Profile', bg=panel, fg=navy,
                 font=('Arial', 10, 'bold')).pack(pady=(10, 4))
        self.profiles = ttk.Combobox(details, textvariable=self.controller_profile,
                                     state='readonly', width=23,
                                     values=['Auto (RetroArch)', 'Atari / Classic', 'NES / SNES',
                                             'Nintendo Switch Pro', 'Xbox',
                                             'PlayStation 3 / 4 / 5', 'Generic USB / Bluetooth'])
        self.profiles.pack(padx=12, fill='x')
        self.profiles.bind('<<ComboboxSelected>>', lambda _: self.save())
        ttk.Checkbutton(details, text='Start fullscreen', variable=self.fullscreen,
                        command=self.save).pack(pady=10)
        self.play_button = ttk.Button(details, text='▶  PLAY GAME', command=self.launch_selected,
                                      style='Primary.TButton', cursor='hand2')
        self.play_button.pack(fill='x', padx=12, pady=(14, 8))
        self._btn_role[self.play_button] = 'primary'
        close_btn = ttk.Button(details, text='Controller Setup', command=self.controller_setup,
                               cursor='hand2')
        close_btn.pack(fill='x', padx=12)
        self._btn_role[close_btn] = 'sidebar'

        bottom = tk.Frame(self, bg='#dfe9f5', padx=16, pady=9)
        bottom.pack(fill='x')
        self.bottom_frame = bottom
        self.status = tk.StringVar(value='Ready')
        self.status_label = tk.Label(bottom, textvariable=self.status, bg='#dfe9f5',
                                     fg='#324b66', anchor='w')
        self.status_label.pack(fill='x')

    # ---------------------------------------------------------------- theme
    def system_is_dark(self):
        """Read the OS appearance when possible; use a light fallback."""
        try:
            if sys.platform == 'darwin':
                r = subprocess.run(['defaults', 'read', '-g', 'AppleInterfaceStyle'],
                                   capture_output=True, text=True, timeout=2)
                return r.returncode == 0 and 'Dark' in r.stdout
            if sys.platform.startswith('win'):
                import winreg
                with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                                    r'Software\Microsoft\Windows\CurrentVersion\Themes\Personalize') as k:
                    return winreg.QueryValueEx(k, 'AppsUseLightTheme')[0] == 0
            return os.environ.get('GTK_THEME', '').lower().endswith(':dark') or \
                os.environ.get('COLOR_SCHEME', '').lower() == 'dark'
        except (OSError, subprocess.TimeoutExpired, ValueError):
            return False

    def change_theme(self):
        self.apply_theme()
        self.save()

    def apply_theme(self):
        mode = self.theme_choice.get()
        dark = self.system_is_dark() if mode == 'System' else mode == 'Dark'
        c = ({'bg': '#151a24', 'panel': '#202838', 'header': '#101827',
              'toolbar': '#192333', 'fg': '#ecf2ff', 'muted': '#b1c1d8',
              'accent': '#397fe0', 'select': '#315887', 'border': '#384860',
              'input': '#111b2a'} if dark else
             {'bg': '#edf2f8', 'panel': '#ffffff', 'header': '#142e52',
              'toolbar': '#dfe9f5', 'fg': '#142e52', 'muted': '#3b526e',
              'accent': '#2b70c9', 'select': '#d8e8ff', 'border': '#ccd9e9',
              'input': '#ffffff'})
        self.configure(bg=c['bg'])
        st = ttk.Style(self)
        if 'clam' in st.theme_names():
            st.theme_use('clam')
        st.configure('Treeview', background=c['input'], fieldbackground=c['input'],
                     foreground=c['fg'], rowheight=32, bordercolor=c['border'])
        st.configure('Treeview.Heading', background=c['toolbar'], foreground=c['fg'],
                     font=('Arial', 10, 'bold'))
        st.map('Treeview', background=[('selected', c['select'])],
               foreground=[('selected', '#ffffff' if dark else c['header'])])
        st.configure('TFrame', background=c['panel'])
        st.configure('TLabel', background=c['panel'], foreground=c['fg'])
        # Every button: black background, blue text, whatever the theme.
        btn_map = dict(background=[('pressed', BTN_BG_PRESSED), ('active', BTN_BG_ACTIVE),
                                   ('disabled', BTN_BG)],
                       foreground=[('pressed', BTN_FG_ACTIVE), ('active', BTN_FG_ACTIVE),
                                   ('disabled', BTN_FG_DISABLED)])
        st.configure('TButton', background=BTN_BG, foreground=BTN_FG,
                     bordercolor=BTN_BORDER, lightcolor=BTN_BG, darkcolor=BTN_BG,
                     focuscolor=BTN_FG, padding=(10, 7), font=('Arial', 10, 'bold'))
        st.map('TButton', **btn_map)
        st.configure('Toolbar.TButton', padding=(10, 6))
        st.map('Toolbar.TButton', **btn_map)
        st.configure('Sidebar.TButton', anchor='w', padding=(14, 9),
                     font=('Arial', 10, 'bold'))
        st.map('Sidebar.TButton', **btn_map)
        st.configure('Primary.TButton', padding=(18, 12), font=('Arial', 12, 'bold'))
        st.map('Primary.TButton', **btn_map)
        st.configure('TCheckbutton', background=c['panel'], foreground=c['fg'])
        st.configure('TEntry', fieldbackground=c['input'], foreground=c['fg'])
        st.configure('TCombobox', fieldbackground=c['input'], foreground=c['fg'])
        st.map('TCombobox', fieldbackground=[('readonly', c['input'])],
               foreground=[('readonly', c['fg'])])

        def repaint(widget):
            if isinstance(widget, tk.Menu):
                return
            if isinstance(widget, (tk.Toplevel, tk.Tk, tk.PanedWindow)):
                widget.configure(bg=c['bg'])
            elif isinstance(widget, tk.Frame):
                if widget is getattr(self, 'header_frame', None):
                    widget.configure(bg=c['header'])
                elif widget in (getattr(self, 'toolbar_frame', None),
                                getattr(self, 'bottom_frame', None)):
                    widget.configure(bg=c['toolbar'])
                elif widget is getattr(self, 'body_frame', None):
                    widget.configure(bg=c['bg'])
                else:
                    widget.configure(bg=c['panel'])
                if widget.cget('highlightthickness'):
                    widget.configure(highlightbackground=c['border'])
            elif isinstance(widget, tk.Label):
                master = widget.master
                parent_bg = master.cget('bg') if 'bg' in master.keys() else c['panel']
                if parent_bg == c['header']:
                    fg = '#ffffff'
                elif widget is getattr(self, 'status_label', None):
                    fg = c['muted']
                else:
                    fg = c['fg']
                widget.configure(bg=parent_bg, fg=fg)
            elif isinstance(widget, tk.Button):
                # Any classic tk.Button that slips in still gets black/blue.
                widget.configure(bg=BTN_BG, fg=BTN_FG, activebackground=BTN_BG_ACTIVE,
                                 activeforeground=BTN_FG_ACTIVE, highlightbackground=BTN_BG,
                                 relief='flat', cursor='hand2')
            for child in widget.winfo_children():
                repaint(child)

        repaint(self)
        try:
            self.menu_bar.configure(bg=c['panel'], fg=c['fg'], activebackground=c['select'])
            for m in (self.file_menu, self.tools_menu, self.help_menu, self.appearance_menu):
                m.configure(bg=c['panel'], fg=c['fg'], activebackground=c['select'])
        except (AttributeError, tk.TclError):
            pass

    # ---------------------------------------------------------------- details
    def update_details(self):
        path = self.selected_path()
        if not path:
            self.detail.set('Select a ROM to view details.')
        else:
            self.detail.set(f'{path.stem}\n\nFormat: {path.suffix.upper().lstrip(".")}\n\n'
                            f'File: {path.name}\n\nDouble-click or press Play.')

    def controller_setup(self):
        dlg = tk.Toplevel(self)
        dlg.title('CatN64Emu — Controller Setup')
        dlg.geometry('590x440')
        dlg.transient(self)
        frame = ttk.Frame(dlg, padding=18)
        frame.pack(fill='both', expand=True)
        ttk.Label(frame, text='Bluetooth & USB Controllers',
                  font=('Arial', 16, 'bold')).pack(anchor='w', pady=(0, 10))
        text = ('CatN64Emu uses RetroArch controller autoconfiguration when the RetroArch backend is active.\n\n'
                '1. Pair your controller in your OS Bluetooth settings.\n'
                '2. Connect via USB if Bluetooth is unsupported.\n'
                '3. Open RetroArch → Settings → Input → RetroPad Binds / Port 1 Controls.\n'
                '4. Use Online Updater → Update Controller Profiles if necessary.\n\n'
                'Supported when drivers and profiles exist: DualSense (PS5), DualShock, Xbox, Switch Pro, '
                'and many generic Bluetooth/USB gamepads.\n\n'
                'Vintage Atari controllers generally need a USB/Bluetooth adapter that exposes standard '
                'gamepad input. Not every Atari device is plug-and-play.\n\n'
                'Note: Native Mupen64Plus controller mapping is configured separately using its input plugin.')
        ttk.Label(frame, text=text, wraplength=535, justify='left').pack(anchor='w')
        ttk.Button(frame, text='Open Bluetooth Settings',
                   command=self.open_bluetooth).pack(anchor='w', pady=(15, 5))
        ttk.Button(frame, text='Close', command=dlg.destroy).pack(anchor='e')
        self.apply_theme()

    def _open_url(self, url):
        try:
            if sys.platform == 'darwin':
                subprocess.Popen(['open', url])
            elif sys.platform.startswith('win'):
                os.startfile(url)                 # noqa: no shell
            else:
                subprocess.Popen(['xdg-open', url])
        except OSError:
            messagebox.showinfo(APP, url)

    def open_bluetooth(self):
        try:
            if sys.platform == 'darwin':
                subprocess.Popen(['open', 'x-apple.systempreferences:com.apple.BluetoothSettings'])
            elif sys.platform.startswith('win'):
                subprocess.Popen(['start', 'ms-settings:bluetooth'], shell=True)
            else:
                messagebox.showinfo('Bluetooth', 'Open your system Bluetooth settings and pair your controller.')
        except OSError as exc:
            messagebox.showerror('Bluetooth settings', str(exc))

    # ---------------------------------------------------------------- settings
    def save(self):
        self.cfg['emulator'] = self.emulator.get().strip()
        self.cfg['core'] = self.core.get().strip()
        self.cfg['extra_args'] = self.extra_args.get().strip()
        self.cfg['controller_profile'] = self.controller_profile.get()
        self.cfg['fullscreen'] = self.fullscreen.get()
        self.cfg['geometry'] = self.geometry()
        self.cfg['theme'] = self.theme_choice.get()
        try:
            CONFIG_DIR.mkdir(parents=True, exist_ok=True)
            CONFIG_FILE.write_text(json.dumps(self.cfg, indent=2), encoding='utf-8')
        except OSError as exc:
            self.status.set('Could not save settings: ' + str(exc))

    # ---------------------------------------------------------------- library
    def add_folder(self):
        folder = filedialog.askdirectory(title='Choose N64 ROM folder')
        if folder and folder not in self.cfg['rom_dirs']:
            self.cfg['rom_dirs'].append(folder)
            self.save()
            self.scan()

    def scan(self):
        """Walk configured folders on a worker thread; results land on the UI thread."""
        if self._scanning:
            self._rescan = True
            return
        self._scanning = True
        self._rescan = False
        self.status.set('Scanning library…')
        threading.Thread(target=self._scan_worker,
                         args=(list(self.cfg.get('rom_dirs', [])),), daemon=True).start()

    def _scan_worker(self, folders):
        self._sweep_temp_dirs()
        games, seen = [], set()
        for folder in folders:
            root = expand(folder)
            if not root.is_dir():
                continue
            try:
                for p in root.rglob('*'):
                    try:
                        if not p.is_file():
                            continue
                    except OSError:
                        continue
                    suffix = p.suffix.lower()
                    if suffix not in ZIP_EXTS:
                        continue
                    key = str(p)
                    if key in seen:
                        continue
                    seen.add(key)
                    if suffix == '.zip':
                        if not zip_has_rom(p):
                            continue
                        name = p.stem
                    else:
                        # .rom/.bin aren't scanned; .z64/.n64/.v64 may be hacks
                        name = read_header(p, lenient=True)
                    if name:
                        games.append((name, p))
            except OSError:
                continue
        games.sort(key=lambda g: g[0].casefold())
        self._ui(lambda: self._scan_done(games))

    def _scan_done(self, games):
        self.games = games
        self._scanning = False
        self.populate()
        if self._rescan:
            self.scan()

    def _sweep_temp_dirs(self):
        """Drop leftovers from crashed sessions; per-launch dirs clean up on exit."""
        try:
            now = time.time()
            for d in Path(tempfile.gettempdir()).glob(TEMP_PREFIX + '*'):
                if d.is_dir() and d != self.tempdir and now - d.stat().st_mtime > TEMP_MAX_AGE:
                    shutil.rmtree(d, ignore_errors=True)
        except OSError:
            pass

    def populate(self):
        if not hasattr(self, 'tree'):
            return
        self.tree.delete(*self.tree.get_children())
        self.visible.clear()
        self.detail.set('Select a ROM to view details.')
        query = self.search.get().strip().casefold()
        for name, path in self.games:
            if query and query not in (name + ' ' + path.name).casefold():
                continue
            item = self.tree.insert('', 'end', values=(name, path.suffix.upper().lstrip('.'), str(path)))
            self.visible[item] = path
        self.status.set(f'{len(self.visible)} games shown  •  {len(self.games)} total  •  '
                        'Double-click to launch')

    def open_file(self):
        f = filedialog.askopenfilename(title='Open Nintendo 64 ROM', filetypes=[
            ('N64 ROMs and ZIPs', '*.z64 *.n64 *.v64 *.zip'), ('All files', '*.*')])
        if f:
            self.launch(Path(f))

    def selected_path(self):
        selected = self.tree.selection()
        return self.visible.get(selected[0]) if selected else None

    def launch_selected(self):
        path = self.selected_path()
        if not path:
            messagebox.showinfo(APP, 'Select a game, or click Open ROM.')
            return
        self.launch(path)

    # ---------------------------------------------------------------- launching
    def prepare_rom(self, path):
        """Return (rom_path, workdir_or_None)."""
        if path.suffix.lower() != '.zip':
            if read_header(path) is None:
                raise ValueError('File is too small to be an N64 ROM.')
            return path, None
        try:
            with ZipFile(path) as archive:
                matches = [i for i in archive.infolist()
                           if not i.is_dir() and Path(i.filename).suffix.lower() in EXTS]
                if not matches:
                    raise ValueError('ZIP archive contains no .z64, .n64, or .v64 ROM.')
                item = matches[0]
                if item.flag_bits & 0x1:
                    raise ValueError('ZIP entry is encrypted; extract the ROM first.')
                if item.file_size > 256 * 1024 * 1024:
                    raise ValueError('ROM exceeds 256 MB safety limit.')
                work = Path(tempfile.mkdtemp(prefix='launch_', dir=self.tempdir))
                # Keep the real file name: RetroArch names saves/states after it.
                stem = ''.join(ch if ch.isalnum() or ch in ' -_.()[]' else '_'
                               for ch in Path(item.filename).stem).strip() or path.stem
                target = work / (stem[:150] + Path(item.filename).suffix.lower())
                with archive.open(item) as src, target.open('wb') as dst:
                    shutil.copyfileobj(src, dst)
                if read_header(target) is None:
                    shutil.rmtree(work, ignore_errors=True)
                    raise ValueError('Archive contains an unrecognized ROM.')
                return target, work
        except BadZipFile as exc:
            raise ValueError('Invalid ZIP archive.') from exc
        except (RuntimeError, EOFError, OSError) as exc:
            raise ValueError(f'Could not read archive: {exc}') from exc

    def _report_crash(self, label, backend, code, log):
        try:
            tail = log.read_text(encoding='utf-8', errors='replace').splitlines()[-25:]
        except OSError:
            tail = []
        low = '\n'.join(tail).lower()
        if 'failed to open libretro core' in low:
            hint = ('RetroArch could not load the N64 core. It is built for a different CPU '
                    'type or RetroArch version. In RetroArch use Online Updater → Core '
                    'Downloader → Nintendo - Nintendo 64 (Mupen64Plus-Next), then '
                    'Tools → Auto-detect Backend here.')
        elif backend == 'RetroArch':
            hint = ('Every safe mode crashed too (OpenGL, interpreter CPU, software video, '
                    'Vulkan). Update RetroArch and the N64 core from RetroArch\'s Online '
                    'Updater. Use Tools → Diagnostics… and send the report.')
        else:
            hint = 'Mupen64Plus exited during boot. The full log shows the exact error.'
        self.status.set(f'{backend} crashed on boot: {label} (exit {code})')
        messagebox.showerror(f'{backend} crashed on boot',
                             f'{label}\n\n{hint}\n\nExit code: {code}\nFull log: {log}\n\n'
                             'Last log lines:\n' + '\n'.join(tail))

    def _game_exited(self):
        self._running = max(0, self._running - 1)

    def _open_log(self, name, argv, append=False):
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        safe = ''.join(ch if ch.isalnum() or ch in '-_.' else '_' for ch in name)[:120]
        log = LOG_DIR / safe
        f = open(log, 'a' if append else 'w', encoding='utf-8', errors='replace')
        f.write(('\n' if append else '') + ' '.join(shlex.quote(a) for a in argv) + '\n\n')
        f.flush()
        return log, f

    def launch(self, path):
        # A stale / wrong saved path used to block auto-detection entirely.
        exe = resolve_emulator(self.emulator.get())
        if exe != self.emulator.get().strip():
            self.emulator.set(exe)
        configured = self.core.get().strip()
        core = resolve_core(configured, exe)   # only cores RetroArch's CPU type can load
        if core != configured:
            self.core.set(core)
        self.save()
        native = discover_standalone()
        if valid_retroarch(exe) and not core:
            arch = target_core_arch(exe)
            if messagebox.askyesno('Download the N64 core?',
                    f'RetroArch was found:\n{exe}\n\nbut it has no N64 core it can load '
                    f'(it needs a {arch} core).\n\nDownload Mupen64Plus-Next ({arch}) from the '
                    'official RetroArch buildbot now and start the game?'):
                self.install_core(arch=arch, then=lambda: self.launch(path))
            return
        if not valid_retroarch(exe) and not native:
            label = retroarch_package()[2]
            if messagebox.askyesno('RetroArch not found',
                    'CatN64Emu could not find RetroArch (checked /Applications, '
                    '~/Applications, Steam, Spotlight and PATH).\n\n'
                    f'Install the official {label} for this computer now (~200–250 MB, into '
                    'the catn64emu_runtime folder) and start the game?\n\n'
                    'Already installed somewhere else? Choose No, then Tools → '
                    'RetroArch / Emulator Settings… → Browse.'):
                self.install_retroarch(then=lambda: self.launch(path))
            return
        if valid_retroarch(exe) and sys.platform == 'darwin' and host_is_arm64() \
                and 'arm64' not in macho_archs(expand(exe)) and not self.cfg.get('rosetta_noted'):
            self.cfg['rosetta_noted'] = True
            self.save()
            if messagebox.askyesno('Intel RetroArch on an Apple M-chip Mac',
                    f'Your RetroArch is an Intel-only build:\n{exe}\n\nIt runs translated by '
                    'Rosetta and can\'t load Apple Silicon cores, which is why games crashed on '
                    'boot.\n\nInstall the official Universal RetroArch (native on M-chips, '
                    '~230 MB) into the catn64emu_runtime folder now and start the game?\n\n'
                    'No = keep this RetroArch and use a matching Intel core instead.'):
                self.install_retroarch(then=lambda: self.launch(path))
                return
        try:
            rom, work = self.prepare_rom(path)
        except (OSError, ValueError) as exc:
            messagebox.showerror('Launch failed', str(exc))
            return
        if work is None:                          # session dir for our config files
            work = Path(tempfile.mkdtemp(prefix='launch_', dir=self.tempdir))
        ctx = {'path': path, 'rom': rom, 'work': work, 'exe': exe, 'core': core,
               'native': native, 'use_ra': retroarch_core_available(exe, core)}
        if ctx['use_ra']:
            prefix, problem = arch_prefix(exe, core)
            if problem:                           # shouldn't happen after resolve_core
                shutil.rmtree(work, ignore_errors=True)
                arch = target_core_arch(exe)
                if messagebox.askyesno('N64 core does not match RetroArch',
                        problem.split('\n\n')[0] + f'\n\nDownload the matching {arch} core now '
                        'and start the game?'):
                    self.install_core(arch=arch, then=lambda: self.launch(path))
                return
            ctx['prefix'] = prefix
            key = str(path)
            ctx['key'] = key
            # Start at the stage that last booted this game (or any game).
            ctx['stage'] = int(self.cfg.get('boot_stage', {}).get(
                key, self.cfg.get('boot_stage_default', 0)))
        self._attempt(ctx, append=False)

    def _attempt(self, ctx, append=True):
        path, work, rom = ctx['path'], ctx['work'], ctx['rom']
        try:
            if ctx['use_ra']:
                exe, core, stage = ctx['exe'], ctx['core'], ctx['stage']
                cfg, opts = stage_session(core, exe, stage)
                cfg_path = work / 'catn64emu.cfg'
                if opts:
                    opt_path = work / 'catn64emu.opt'
                    opt_path.write_text(''.join(f'{k} = "{v}"\n' for k, v in opts.items()),
                                        encoding='utf-8')
                    cfg.update(core_options_path=str(opt_path), global_core_options='true',
                               game_specific_options='false')
                cfg_path.write_text(''.join(f'{k} = "{v}"\n' for k, v in cfg.items()),
                                    encoding='utf-8')
                args = shlex.split(self.extra_args.get())
                if self.fullscreen.get() and '--fullscreen' not in args and '-f' not in args:
                    args.append('--fullscreen')
                if '--verbose' not in args and '-v' not in args:
                    args.append('--verbose')           # crash reasons land in the log
                args = merge_appendconfig(args, str(cfg_path))
                target = expand(exe)
                argv = [*ctx['prefix'], str(target), '-L', str(expand(core)), *args, str(rom)]
                log, logf = self._open_log(f'retroarch-{path.stem}.log', argv, append)
                with logf:
                    logf.write(f'===== CatN64Emu stage {stage}: {SAFE_STAGES[stage]} =====\n')
                    logf.flush()
                    env = dict(os.environ)
                    if target.suffix == '.AppImage':
                        env['APPIMAGE_EXTRACT_AND_RUN'] = '1'   # works without FUSE
                    proc = subprocess.Popen(argv, stdout=logf, stderr=subprocess.STDOUT,
                                            stdin=subprocess.DEVNULL, env=env,
                                            cwd=str(target.resolve().parent) if target.is_file() else None)
                backend = 'RetroArch'
                note = f'  •  safe mode {stage}: {SAFE_STAGES[stage]}' if stage else ''
            else:
                native_path = expand(ctx['native'])
                argv = [str(native_path),
                        '--fullscreen' if self.fullscreen.get() else '--windowed', str(rom)]
                log, logf = self._open_log(f'mupen64plus-{path.stem}.log', argv)
                with logf:
                    proc = subprocess.Popen(argv, stdout=logf, stderr=subprocess.STDOUT,
                                            stdin=subprocess.DEVNULL, cwd=str(native_path.parent))
                backend, note = 'Mupen64Plus', ''
            self.status.set(f'{backend} launched: {path.name}{note}')
        except (OSError, ValueError) as exc:
            shutil.rmtree(work, ignore_errors=True)
            messagebox.showerror('Launch failed', str(exc))
            return
        ctx.update(log=log, backend=backend)
        self._watch(proc, ctx)

    def _watch(self, proc, ctx):
        """Wait for the emulator; on a crash during boot retry safer, else clean up."""
        started = time.monotonic()
        self._running += 1

        def wait():
            try:
                code = proc.wait()
            except OSError:
                code = -1
            elapsed = time.monotonic() - started
            try:
                text = ctx['log'].read_text(encoding='utf-8', errors='replace').lower()
                text = text[text.rfind('===== catn64emu stage'):]   # this attempt only
            except OSError:
                text = ''
            failed = any(m in text for m in BOOT_FAIL_MARKERS)
            crashed = elapsed < BOOT_WINDOW and (code not in (0, None) or failed)
            self._ui(lambda: self._attempt_done(ctx, code, crashed, text))
        threading.Thread(target=wait, daemon=True).start()

    def _attempt_done(self, ctx, code, crashed, text):
        self._game_exited()
        if ctx['use_ra']:
            fatal = 'failed to open libretro core' in text
            if crashed and not fatal and ctx['stage'] + 1 < len(SAFE_STAGES):
                ctx['stage'] += 1
                self.status.set(f'{ctx["path"].name} crashed on boot (exit {code}) — retrying '
                                f'with {SAFE_STAGES[ctx["stage"]]}…')
                self.after(500, lambda: self._attempt(ctx))
                return
            if not crashed:
                if ctx['stage']:
                    # Remember what boots; most Macs need the same stage for every game.
                    self.cfg.setdefault('boot_stage', {})[ctx['key']] = ctx['stage']
                    self.cfg['boot_stage_default'] = ctx['stage']
                    self.save()
            else:
                self.cfg.get('boot_stage', {}).pop(ctx['key'], None)
                self.save()
        shutil.rmtree(ctx['work'], ignore_errors=True)
        if crashed:
            self._report_crash(ctx['path'].name, ctx['backend'], code, ctx['log'])

    # ---------------------------------------------------------------- installers
    def install_native_backend(self, pending_rom=None):
        """Install a real emulator through the platform package manager."""
        osname = platform.system()
        if osname == 'Darwin':
            brew = shutil.which('brew')
            if not brew:
                messagebox.showerror('Homebrew required',
                    'Install Homebrew first, or install Mupen64Plus manually:\n\n'
                    'https://brew.sh')
                return
            command = [brew, 'install', 'mupen64plus']
        elif osname == 'Linux':
            hints = {'apt-get': ['sudo', 'apt-get', 'install', '-y', 'mupen64plus'],
                     'dnf': ['sudo', 'dnf', 'install', '-y', 'mupen64plus'],
                     'pacman': ['sudo', 'pacman', '-S', '--noconfirm', 'mupen64plus']}
            for tool, cmd in hints.items():
                if shutil.which(tool):
                    command = cmd
                    break
            else:
                messagebox.showerror('Package manager not found',
                    'Install Mupen64Plus with your distribution package manager, then retry.')
                return
        else:
            messagebox.showerror('Automatic install unavailable',
                'Download Mupen64Plus for your platform, or use RetroArch with an N64 core.')
            return
        self.status.set('Installing native Mupen64Plus…')
        def work():
            try:
                result = subprocess.run(command, capture_output=True, text=True, timeout=900)
                if result.returncode:
                    detail = (result.stderr or result.stdout)[-1600:]
                    raise RuntimeError(detail or 'Installation failed')
                exe = discover_standalone()
                if not exe:
                    raise RuntimeError('Package manager finished but mupen64plus was not found.')
                def success():
                    self.status.set('Mupen64Plus installed: ' + exe)
                    if pending_rom:
                        self.launch(pending_rom)
                    else:
                        messagebox.showinfo('N64 backend installed',
                                            'Mupen64Plus is ready. Select a ROM to play.')
                self._ui(success)
            except Exception as exc:
                self._ui(lambda msg=str(exc): messagebox.showerror(
                    'Mupen64Plus installation failed', msg))
        threading.Thread(target=work, daemon=True).start()

    def install_retroarch(self, then=None):
        """Install the official RetroArch for this OS/CPU, then a matching N64 core."""
        if getattr(self, '_installing', False):
            self.status.set('An install is already running…')
            return
        self._installing = True
        self.status.set('Preparing RetroArch install…')

        def progress(msg):
            self._ui(lambda m=msg: self.status.set(m))

        def work():
            try:
                exe = install_native_retroarch(progress)
                if is_bsd():
                    core = discover_core(str(exe))
                    if not core:
                        raise RuntimeError('RetroArch is installed, but no N64 core package was '
                                           'found. Open RetroArch → Online Updater → Core '
                                           'Downloader → Nintendo 64, then Tools → Auto-detect.')
                else:
                    arch = target_core_arch(str(exe))
                    progress(f'Downloading the {arch} N64 core…')
                    core = download_n64_core(progress, arch)

                def done():
                    self._installing = False
                    self.emulator.set(str(exe))
                    self.core.set(core)
                    self.cfg['boot_stage'] = {}
                    self.cfg['boot_stage_default'] = 0
                    self.cfg['rosetta_noted'] = False
                    self.save()
                    self.status.set(f'RetroArch installed: {exe}  •  core: {Path(core).name}')
                    if then:
                        then()
                    else:
                        messagebox.showinfo('RetroArch installed',
                                            f'RetroArch: {exe}\nN64 core: {core}\n\n'
                                            'Select a game and press Play.')
                self._ui(done)
            except Exception as exc:
                def fail(msg=str(exc)):
                    self._installing = False
                    self.status.set('RetroArch install failed.')
                    messagebox.showerror('RetroArch install failed', msg)
                self._ui(fail)
        threading.Thread(target=work, daemon=True).start()

    def install_core(self, arch=None, then=None):
        exe = resolve_emulator(self.emulator.get())
        arch = arch or target_core_arch(exe)      # match RetroArch's CPU type, not Python's
        self.status.set(f'Checking for an official {arch} N64 core…')
        def progress(msg):
            self._ui(lambda m=msg: self.status.set(m))
        def work():
            try:
                core = download_n64_core(progress, arch)
                def done():
                    self.core.set(core)
                    self.save()
                    if then:
                        self.status.set('N64 core installed: ' + Path(core).name)
                        then()
                        return
                    messagebox.showinfo('N64 core installed',
                        'Installed: ' + core + '\nYou can now launch games if RetroArch is installed.')
                self._ui(done)
            except Exception as exc:
                self._ui(lambda msg=str(exc): messagebox.showerror('Core installation failed', msg))
        threading.Thread(target=work, daemon=True).start()

    def autodetect(self):
        exe = discover_emulator()
        if exe:
            self.emulator.set(exe)
        self.cfg['rosetta_noted'] = False
        self.cfg.pop('setup_declined', None)
        core = discover_core(self.emulator.get())
        self.core.set(core)
        self.cfg['boot_stage'] = {}               # re-test boot modes for the new backend
        self.cfg['boot_stage_default'] = 0
        self.save()
        self.status.set(('RetroArch found' if exe else 'RetroArch not found') +
                        (' • N64 core found' if core
                         else (' • Native Mupen64Plus available' if discover_standalone()
                               else ' • N64 backend missing')))

    def configure_emulator(self):
        dialog = tk.Toplevel(self)
        dialog.title('RetroArch + N64 Core Setup')
        dialog.geometry('750x320')
        dialog.transient(self)
        dialog.grab_set()
        dialog.columnconfigure(1, weight=1)
        tk.Label(dialog, text='RetroArch executable:').grid(row=0, column=0, padx=12, pady=12, sticky='w')
        ttk.Entry(dialog, textvariable=self.emulator).grid(row=0, column=1, sticky='ew', padx=5)
        ttk.Button(dialog, text='Browse…', command=self._browse_emulator).grid(row=0, column=2, padx=12)
        tk.Label(dialog, text='N64 libretro core:').grid(row=1, column=0, padx=12, pady=12, sticky='w')
        ttk.Entry(dialog, textvariable=self.core).grid(row=1, column=1, sticky='ew', padx=5)
        ttk.Button(dialog, text='Browse…', command=self._browse_core).grid(row=1, column=2, padx=12)
        tk.Label(dialog, text='Extra RetroArch arguments:').grid(row=2, column=0, padx=12, pady=8, sticky='w')
        ttk.Entry(dialog, textvariable=self.extra_args).grid(row=2, column=1, columnspan=2, sticky='ew', padx=5)
        info = ('Portable runtime: put RetroArch in catn64emu_runtime/ and your N64 core in\n'
                'catn64emu_runtime/cores/. The launcher auto-selects the core with -L.\n'
                'Alternatively install RetroArch and download Mupen64Plus-Next in its Online Updater.\n'
                'If RetroArch has no compatible core, CatN64Emu uses native Mupen64Plus.\n'
                'Install N64 Backend uses your platform package manager.')
        tk.Label(dialog, text=info, justify='left').grid(row=3, column=0, columnspan=3,
                                                         padx=12, pady=12, sticky='w')
        ttk.Button(dialog, text='Install N64 Backend',
                  command=self.install_native_backend).grid(row=4, column=0, padx=12, pady=8)
        ttk.Button(dialog, text='Auto-detect',
                  command=self.autodetect).grid(row=4, column=1, sticky='e', pady=8)
        ttk.Button(dialog, text='Save Settings',
                  command=lambda: (self.save(), dialog.destroy()),
                  ).grid(row=4, column=2, padx=12, pady=8)
        self.apply_theme()                      # new Toplevel picks up the current theme

    def diagnostics(self):
        """One copy-pasteable report of everything that decides whether a game boots."""
        exe = resolve_emulator(self.emulator.get())
        core = resolve_core(self.core.get().strip(), exe)
        lines = [f'{APP} diagnostics',
                 f'OS: {platform.platform()}',
                 f'Python: {sys.version.split()[0]} ({platform.machine()}) at {sys.executable}',
                 f'Host CPU: {"arm64 (Apple Silicon)" if host_is_arm64() else platform.machine()}',
                 f'RetroArch: {exe or "NOT FOUND"}',
                 f'  arch: {"/".join(sorted(macho_archs(expand(exe)))) or "n/a"}' if exe else '',
                 f'Core: {core or "NOT FOUND"}',
                 f'  arch: {"/".join(sorted(macho_archs(expand(core)))) or "n/a"}' if core else '',
                 f'Native Mupen64Plus: {discover_standalone() or "not installed"}',
                 f'GPU: {gpu_info()[0]} — {gpu_info()[1]}',
                 f'Native RetroArch package for this computer: {retroarch_package()[2]}',
                 'Boot fallback order: ' + ' → '.join(st[0] for st in stages()),
                 'RetroArch copies found: ' + ('; '.join(
                     f'{c} [{"/".join(sorted(macho_archs(c))) or "?"}]'
                     for c in emulator_candidates()) or 'none'),
                 'N64 cores found: ' + ('; '.join(
                     f'{c} [{"/".join(sorted(macho_archs(c))) or "?"}]'
                     for c in core_candidates(exe)) or 'none')]
        if exe and core:
            prefix, problem = arch_prefix(exe, core)
            lines.append(f'Launch prefix: {" ".join(prefix) or "(none)"}'
                         + (f'  PROBLEM: {problem.splitlines()[0]}' if problem else ''))
            lines.append(f'Video driver used at stage 0: {n64_video_driver(core, exe)}')
        if exe:
            try:
                prefix = arch_prefix(exe, core)[0] if core else []
                r = subprocess.run([*prefix, str(expand(exe)), '--version'], capture_output=True,
                                   text=True, timeout=10)
                ver = (r.stdout + r.stderr).strip().splitlines()
                lines.append('RetroArch --version: ' + (' | '.join(ver[:3]) or f'exit {r.returncode}'))
            except (OSError, subprocess.TimeoutExpired) as exc:
                lines.append(f'RetroArch --version failed: {exc}')
        for d in retroarch_config_dirs(exe):
            cfg = d / 'retroarch.cfg'
            if cfg.is_file():
                try:
                    for line in cfg.read_text(encoding='utf-8', errors='replace').splitlines():
                        if line.split('=')[0].strip() in ('video_driver', 'libretro_directory',
                                                          'video_context_driver'):
                            lines.append(f'{cfg}: {line.strip()}')
                except OSError:
                    pass
                break
        for key in ('mupen64plus-rdp-plugin', 'mupen64plus-cpucore', 'mupen64plus-rsp-plugin'):
            lines.append(f'Saved core option {key}: {user_core_option(exe, key) or "(default)"}')
        lines.append(f'Remembered boot stages: {self.cfg.get("boot_stage", {})} '
                     f'default={self.cfg.get("boot_stage_default", 0)}')
        logs = sorted(LOG_DIR.glob('*.log'), key=lambda f: f.stat().st_mtime) if LOG_DIR.is_dir() else []
        if logs:
            try:
                tail = logs[-1].read_text(encoding='utf-8', errors='replace').splitlines()[-40:]
            except OSError:
                tail = []
            lines += ['', f'--- last 40 lines of {logs[-1].name} ---', *tail]
        report = '\n'.join(l for l in lines if l != '')

        dlg = tk.Toplevel(self)
        dlg.title('CatN64Emu — Diagnostics')
        dlg.geometry('820x560')
        dlg.transient(self)
        frame = ttk.Frame(dlg, padding=12)
        frame.pack(fill='both', expand=True)
        ttk.Label(frame, text='Copy this report and paste it into your bug report.'
                  ).pack(anchor='w', pady=(0, 6))
        box = tk.Text(frame, wrap='none', font=('Menlo', 10), height=24)
        box.insert('1.0', report)
        box.pack(fill='both', expand=True)

        def copy():
            self.clipboard_clear()
            self.clipboard_append(report)
            self.status.set('Diagnostics copied to clipboard.')
        row = ttk.Frame(frame)
        row.pack(fill='x', pady=(8, 0))
        ttk.Button(row, text='Copy Report', command=copy).pack(side='left')
        ttk.Button(row, text='Close', command=dlg.destroy).pack(side='right')
        self.apply_theme()
        return report

    def _browse_emulator(self):
        f = filedialog.askopenfilename(title='Choose RetroArch executable')
        if f:
            f = normalize_exe(f)
            self.emulator.set(f)
            if not self.core.get():
                self.core.set(discover_core(f))

    def _browse_core(self):
        f = filedialog.askopenfilename(title='Choose N64 libretro core',
                                       filetypes=[('Libretro cores', '*.dylib *.so *.dll'),
                                                  ('All files', '*.*')])
        if f:
            self.core.set(f)

    def close(self):
        try:
            self.save()
        finally:
            # Per-launch extraction dirs are removed when the emulator exits;
            # this one goes on the next start if anything is still inside.
            # A running game still needs its extracted ROM; the startup sweep
            # removes this folder later instead.
            if not self._running:
                try:
                    shutil.rmtree(self.tempdir, ignore_errors=True)
                except OSError:
                    pass
            self.destroy()


if __name__ == '__main__':
    try:
        Launcher().mainloop()
    except tk.TclError as exc:
        print('Tkinter GUI unavailable:', exc, file=sys.stderr)
        sys.exit(1)