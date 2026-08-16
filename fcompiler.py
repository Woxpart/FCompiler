#!/usr/bin/env python3
"""
FCompiler v5.0 — Task graph, conflict mediation, APT, parallel modules, JDK bootstrap

  • Transitive deps (POM) + lockfile (dependencies.lock)
  • Multi-module reactor
  • Incremental compile + parallel downloads
  • Test phase
  • Plugin system (.fcompiler/plugins/*.py)
  • IDE: Eclipse / IntelliJ / VS Code project files

  python fcompiler.py init myapp
  python fcompiler.py lock
  python fcompiler.py build
  python fcompiler.py ide vscode
"""

from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import threading
import time
import urllib.request
import xml.etree.ElementTree as ET
import zipfile
from collections import defaultdict, deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

# Runtime javac/java (may point to bootstrapped JDK)
_javac_cmd = "javac"
_java_cmd = "java"

try:
    import tomllib
except ImportError:
    try:
        import tomli as tomllib  # type: ignore
    except ImportError:
        tomllib = None  # type: ignore

try:
    import yaml
except ImportError:
    yaml = None  # type: ignore

VERSION = "5.0.0"
USER_AGENT = f"FCompiler/{VERSION}"

# ── terminal ───────────────────────────────────────────────
class _C:
    if os.name == "nt":
        try:
            import ctypes
            h = ctypes.windll.kernel32.GetStdHandle(-11)
            m = ctypes.c_uint32()
            ctypes.windll.kernel32.GetConsoleMode(h, ctypes.byref(m))
            ctypes.windll.kernel32.SetConsoleMode(h, m.value | 0x0004)
        except Exception:
            pass
    C, G, Y, R, B = "\033[96m", "\033[92m", "\033[93m", "\033[91m", "\033[94m"
    Bold, Dim, Reset = "\033[1m", "\033[2m", "\033[0m"

_quiet = _verbose = _no_color = False
_lock = threading.Lock()

def _col(c, t):
    if _no_color or not sys.stdout.isatty():
        return t
    return f"{c}{t}{_C.Reset}"

def log_info(m):
    if not _quiet:
        with _lock: print(f"{_col(_C.C,'[INFO]')} {m}")
def log_ok(m):
    if not _quiet:
        with _lock: print(f"{_col(_C.G,'[OK]')} {m}")
def log_warn(m):
    with _lock: print(f"{_col(_C.Y,'[WARN]')} {m}", file=sys.stderr)
def log_err(m):
    with _lock: print(f"{_col(_C.R,'[ERROR]')} {m}", file=sys.stderr)
def log_step(m):
    if not _quiet:
        with _lock: print(f"{_col(_C.Bold+_C.B,'==>')} {m}")
def log_debug(m):
    if _verbose and not _quiet:
        with _lock: print(f"{_col(_C.Dim,'[DEBUG]')} {m}")

# ── models ─────────────────────────────────────────────────
@dataclass(frozen=True)
class Coord:
    group: str
    artifact: str
    version: str
    def key(self) -> str: return f"{self.group}:{self.artifact}"
    def full(self) -> str: return f"{self.group}:{self.artifact}:{self.version}"
    def maven_rel(self, ext="jar") -> str:
        return f"{self.group.replace('.','/')}/{self.artifact}/{self.version}/{self.artifact}-{self.version}.{ext}"

@dataclass
class Dep:
    coord: Coord
    scope: str = "compile"
    optional: bool = False

@dataclass
class ModuleConfig:
    name: str
    root: Path
    group_id: str = "com.example"
    version: str = "1.0.0"
    main_class: Optional[str] = None
    java_version: str = "17"
    encoding: str = "UTF-8"
    debug: bool = False
    conflict_strategy: str = "nearest"  # nearest | newest | fail | prefer
    prefer: Dict[str, str] = field(default_factory=dict)  # ga -> forced version
    annotation_processors: List[str] = field(default_factory=list)
    processor_path_deps: List[Dep] = field(default_factory=list)
    src_dir: Path = field(default_factory=Path)
    test_src_dir: Path = field(default_factory=Path)
    resources_dir: Path = field(default_factory=Path)
    test_resources_dir: Path = field(default_factory=Path)
    build_dir: Path = field(default_factory=Path)
    classes_dir: Path = field(default_factory=Path)
    test_classes_dir: Path = field(default_factory=Path)
    lib_dir: Path = field(default_factory=Path)
    jar_dir: Path = field(default_factory=Path)
    deps: List[Dep] = field(default_factory=list)
    managed: Dict[str, str] = field(default_factory=dict)  # ga -> version (BOM)
    module_deps: List[str] = field(default_factory=list)
    repositories: List[str] = field(default_factory=list)
    plugins_cfg: List[Any] = field(default_factory=list)

    def finalize_paths(self):
        if not self.src_dir or self.src_dir == Path():
            self.src_dir = self.root / "src"
        if not self.test_src_dir or self.test_src_dir == Path():
            self.test_src_dir = self.root / "src" / "test" / "java"
            if not self.test_src_dir.exists() and (self.root / "test").exists():
                self.test_src_dir = self.root / "test"
        if not self.resources_dir or self.resources_dir == Path():
            self.resources_dir = self.root / "resources"
        if not self.test_resources_dir or self.test_resources_dir == Path():
            self.test_resources_dir = self.root / "src" / "test" / "resources"
        if not self.build_dir or self.build_dir == Path():
            self.build_dir = self.root / "build"
        self.classes_dir = self.build_dir / "classes"
        self.test_classes_dir = self.build_dir / "test-classes"
        self.lib_dir = self.build_dir / "libs"
        self.jar_dir = self.build_dir / "jar"

    @property
    def artifact_name(self): return f"{self.name}-{self.version}"
    @property
    def jar_name(self): return f"{self.artifact_name}.jar"
    @property
    def fat_jar_name(self): return f"{self.artifact_name}-with-dependencies.jar"

@dataclass
class Project:
    root: Path
    name: str
    version: str
    group_id: str
    modules: List[ModuleConfig] = field(default_factory=list)
    repositories: List[str] = field(default_factory=lambda: [
        "https://repo1.maven.org/maven2/",
        "https://repo.maven.apache.org/maven2/",
    ])
    is_multi: bool = False
    managed: Dict[str, str] = field(default_factory=dict)

# ── Plugin system ──────────────────────────────────────────
# ── JDK bootstrap (Temurin) ────────────────────────────────
def _jdk_home_cache() -> Path:
    return Path.home() / ".fcompiler" / "jdk"


def ensure_jdk(preferred: str = "17") -> Tuple[bool, str]:
    """Use PATH javac, or cached/bootstrapped Temurin JDK."""
    global _javac_cmd, _java_cmd
    try:
        r = subprocess.run(["javac", "-version"], capture_output=True, text=True)
        if r.returncode == 0:
            _javac_cmd, _java_cmd = "javac", "java"
            return True, (r.stderr or r.stdout or "").strip()
    except FileNotFoundError:
        pass
    cache = _jdk_home_cache()
    for cand in sorted(cache.glob(f"jdk-{preferred}*")):
        javac = cand / "bin" / ("javac.exe" if os.name == "nt" else "javac")
        java = cand / "bin" / ("java.exe" if os.name == "nt" else "java")
        if javac.exists():
            _javac_cmd, _java_cmd = str(javac), str(java)
            r = subprocess.run([_javac_cmd, "-version"], capture_output=True, text=True)
            return True, (r.stderr or r.stdout or "").strip()
    log_warn("javac bulunamadı — Eclipse Temurin JDK indiriliyor (bir kez)...")
    sysname = platform.system().lower()
    os_name = "mac" if sysname == "darwin" else ("windows" if sysname == "windows" else "linux")
    arch = "x64" if platform.machine().lower() in ("x86_64", "amd64") else "aarch64"
    url = (
        f"https://api.adoptium.net/v3/binary/latest/{preferred}/ga/"
        f"{os_name}/{arch}/jdk/hotspot/normal/eclipse?project=jdk"
    )
    cache.mkdir(parents=True, exist_ok=True)
    archive = cache / f"temurin-{preferred}.bin"
    try:
        log_info(f"JDK indirme: {url}")
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(req, timeout=300) as resp:
            data = resp.read()
        archive.write_bytes(data)
        extract = cache / f"ext-{preferred}"
        if extract.exists():
            shutil.rmtree(extract)
        extract.mkdir()
        if data[:2] == b"PK":
            zipfile.ZipFile(archive).extractall(extract)
        else:
            tarfile.open(archive, "r:*").extractall(extract)
        found = list(extract.rglob("javac.exe" if os.name == "nt" else "javac"))
        if not found:
            return False, "JDK arşivinde javac yok"
        home = found[0].parent.parent
        final = cache / f"jdk-{preferred}"
        if final.exists():
            shutil.rmtree(final)
        shutil.move(str(home), str(final))
        archive.unlink(missing_ok=True)
        shutil.rmtree(extract, ignore_errors=True)
        _javac_cmd = str(final / "bin" / ("javac.exe" if os.name == "nt" else "javac"))
        _java_cmd = str(final / "bin" / ("java.exe" if os.name == "nt" else "java"))
        r = subprocess.run([_javac_cmd, "-version"], capture_output=True, text=True)
        log_ok(f"JDK kuruldu: {final}")
        return True, (r.stderr or r.stdout or "").strip()
    except Exception as e:
        return False, f"JDK bootstrap başarısız: {e}"


HOOKS = (
    "before_resolve", "after_resolve",
    "before_compile", "after_compile",
    "before_package", "after_package",
    "before_test", "after_test",
    "before_build", "after_build",
)

class PluginAPI:
    """Plugins register callbacks via api.on(hook, fn)."""
    def __init__(self):
        self._hooks: Dict[str, List[Callable]] = {h: [] for h in HOOKS}
        self.config: Dict[str, Any] = {}
        self.project: Optional[Project] = None
        self.module: Optional[ModuleConfig] = None

    def on(self, hook: str, fn: Callable):
        if hook not in self._hooks:
            log_warn(f"Bilinmeyen hook: {hook}")
            return
        self._hooks[hook].append(fn)

    def emit(self, hook: str, **ctx) -> bool:
        """Run hooks; if any returns False, abort."""
        for fn in self._hooks.get(hook, []):
            try:
                r = fn(self, **ctx)
                if r is False:
                    log_err(f"Plugin hook '{hook}' iptal etti: {getattr(fn, '__module__', fn)}")
                    return False
            except Exception as e:
                log_err(f"Plugin hatası [{hook}]: {e}")
                if _verbose:
                    import traceback
                    traceback.print_exc()
                return False
        return True

def load_plugins(proj: Project, mod: Optional[ModuleConfig] = None) -> PluginAPI:
    api = PluginAPI()
    api.project = proj
    api.module = mod
    dirs = [
        proj.root / ".fcompiler" / "plugins",
        proj.root / "plugins",
    ]
    if mod:
        dirs.append(mod.root / "plugins")
        dirs.append(mod.root / ".fcompiler" / "plugins")
    seen = set()
    for d in dirs:
        if not d.exists():
            continue
        for py in sorted(d.glob("*.py")):
            if py.name.startswith("_") or py in seen:
                continue
            seen.add(py)
            try:
                spec = importlib.util.spec_from_file_location(f"fc_plugin_{py.stem}", py)
                if not spec or not spec.loader:
                    continue
                module = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(module)
                if hasattr(module, "register"):
                    module.register(api)
                    log_debug(f"Plugin yüklendi: {py.name}")
                else:
                    log_warn(f"Plugin 'register(api)' yok: {py.name}")
            except Exception as e:
                log_err(f"Plugin yüklenemedi {py}: {e}")
    # config from projectinfo [plugins]
    return api

# ── config load ────────────────────────────────────────────
def _parse_dep_entry(d) -> Optional[Dep]:
    if isinstance(d, str):
        parts = d.strip().split(":")
        if len(parts) < 3:
            return None
        return Dep(Coord(parts[0], parts[1], parts[2]), scope=parts[3] if len(parts) > 3 else "compile")
    if isinstance(d, dict):
        g = d.get("groupId") or d.get("group") or ""
        a = d.get("artifactId") or d.get("artifact") or ""
        v = str(d.get("version") or "")
        if not (g and a and v):
            return None
        return Dep(Coord(g, a, v), scope=d.get("scope", "compile"), optional=bool(d.get("optional", False)))
    return None

def _load_managed(data: dict) -> Dict[str, str]:
    managed = {}
    dm = data.get("dependencyManagement") or data.get("bom") or {}
    for entry in dm.get("dependencies") or []:
        if isinstance(entry, str):
            p = entry.split(":")
            if len(p) >= 3:
                managed[f"{p[0]}:{p[1]}"] = p[2]
        elif isinstance(entry, dict):
            g = entry.get("groupId") or entry.get("group") or ""
            a = entry.get("artifactId") or entry.get("artifact") or ""
            v = str(entry.get("version") or "")
            if g and a and v:
                managed[f"{g}:{a}"] = v
    return managed

def _load_module(root: Path, default_repos: List[str], parent_managed: Dict[str, str]) -> Optional[ModuleConfig]:
    toml_path = root / "projectinfo.toml"
    yml_path = root / "dependencies.yml"
    if not toml_path.exists() or tomllib is None:
        return None
    with open(toml_path, "rb") as f:
        data = tomllib.load(f)
    p = data.get("project", {})
    b = data.get("build", {})
    res = data.get("resolution", {})
    ann = data.get("annotationProcessing") or data.get("annotation_processing") or {}
    mod = ModuleConfig(
        name=p.get("name", root.name),
        root=root,
        group_id=p.get("groupId", p.get("group_id", "com.example")),
        version=str(p.get("version", "1.0.0")),
        main_class=p.get("mainClass", p.get("main_class")),
        java_version=str(p.get("javaVersion", p.get("java_version", "17"))),
        encoding=p.get("encoding", "UTF-8"),
        debug=bool(p.get("debug", False)),
        conflict_strategy=res.get("conflict", "nearest"),
        repositories=list(default_repos),
        managed=dict(parent_managed),
    )
    if isinstance(res.get("prefer"), dict):
        mod.prefer.update({str(k): str(v) for k, v in res["prefer"].items()})
    if isinstance(ann.get("processors"), list):
        mod.annotation_processors = list(ann["processors"])
    for pe in ann.get("processorPath") or ann.get("processor_path") or []:
        d = _parse_dep_entry(pe)
        if d:
            mod.processor_path_deps.append(d)
    mod.managed.update(_load_managed(data))
    if "sourceDir" in b: mod.src_dir = root / b["sourceDir"]
    if "testSourceDir" in b: mod.test_src_dir = root / b["testSourceDir"]
    if "resourcesDir" in b: mod.resources_dir = root / b["resourcesDir"]
    if "outputDir" in b: mod.build_dir = root / b["outputDir"]
    mod.finalize_paths()
    repos = data.get("repositories", {})
    if isinstance(repos.get("urls"), list):
        mod.repositories = list(repos["urls"]) + [r for r in default_repos if r not in repos["urls"]]
    mods = data.get("modules", {})
    if isinstance(mods.get("dependsOn"), list):
        mod.module_deps = list(mods["dependsOn"])
    if yml_path.exists():
        if yaml is None:
            log_err("PyYAML gerekli: pip install pyyaml")
            return None
        with open(yml_path, "r", encoding="utf-8") as f:
            dep_data = yaml.safe_load(f) or {}
        mod.managed.update(_load_managed(dep_data))
        for entry in dep_data.get("dependencies") or []:
            # version from BOM if missing
            if isinstance(entry, dict) and not entry.get("version"):
                g = entry.get("groupId") or entry.get("group") or ""
                a = entry.get("artifactId") or entry.get("artifact") or ""
                if f"{g}:{a}" in mod.managed:
                    entry = dict(entry)
                    entry["version"] = mod.managed[f"{g}:{a}"]
            dep = _parse_dep_entry(entry)
            if dep:
                # apply BOM override if managed has version and strategy says so
                ga = dep.coord.key()
                if ga in mod.managed and dep.coord.version != mod.managed[ga]:
                    # keep explicit version unless empty
                    pass
                mod.deps.append(dep)
            elif isinstance(entry, dict):
                g = entry.get("groupId") or entry.get("group") or ""
                a = entry.get("artifactId") or entry.get("artifact") or ""
                v = mod.managed.get(f"{g}:{a}", "")
                if g and a and v:
                    mod.deps.append(Dep(Coord(g, a, v), scope=entry.get("scope", "compile")))
    return mod

def load_project(root: Path) -> Optional[Project]:
    root = root.resolve()
    if not (root / "projectinfo.toml").exists():
        log_err(f"projectinfo.toml yok: {root}")
        return None
    if tomllib is None:
        log_err("tomllib/tomli gerekli")
        return None
    with open(root / "projectinfo.toml", "rb") as f:
        data = tomllib.load(f)
    p = data.get("project", {})
    name = p.get("name", root.name)
    version = str(p.get("version", "1.0.0"))
    group_id = p.get("groupId", p.get("group_id", "com.example"))
    repos = ["https://repo1.maven.org/maven2/", "https://repo.maven.apache.org/maven2/"]
    rsec = data.get("repositories", {})
    if isinstance(rsec.get("urls"), list):
        repos = list(rsec["urls"]) + [x for x in repos if x not in rsec["urls"]]
    managed = _load_managed(data)
    modules_sec = data.get("modules", {})
    module_names = modules_sec.get("list") or modules_sec.get("modules") or []
    if not module_names and (root / "modules.yml").exists() and yaml:
        with open(root / "modules.yml", "r", encoding="utf-8") as f:
            module_names = (yaml.safe_load(f) or {}).get("modules") or []
    proj = Project(root=root, name=name, version=version, group_id=group_id, repositories=repos, managed=managed)
    if module_names:
        proj.is_multi = True
        for mname in module_names:
            mod = _load_module(root / mname, repos, managed)
            if not mod:
                log_err(f"Modül yüklenemedi: {mname}")
                return None
            proj.modules.append(mod)
    else:
        mod = _load_module(root, repos, managed)
        if not mod:
            return None
        proj.modules.append(mod)
    return proj

def topological_modules(modules: List[ModuleConfig]) -> List[ModuleConfig]:
    by_name = {m.name: m for m in modules}
    indeg = {m.name: 0 for m in modules}
    graph: Dict[str, List[str]] = defaultdict(list)
    for m in modules:
        for dep in m.module_deps:
            if dep not in by_name:
                log_warn(f"Bilinmeyen modül: {m.name} → {dep}")
                continue
            graph[dep].append(m.name)
            indeg[m.name] += 1
    q = deque([n for n, d in indeg.items() if d == 0])
    order = []
    while q:
        n = q.popleft()
        order.append(n)
        for nxt in graph[n]:
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                q.append(nxt)
    if len(order) != len(modules):
        log_err("Modül döngüsü")
        return modules
    return [by_name[n] for n in order]

# ── Lockfile ───────────────────────────────────────────────
def lock_path(proj: Project) -> Path:
    return proj.root / "dependencies.lock"

def load_lock(proj: Project) -> Optional[Dict[str, Any]]:
    p = lock_path(proj)
    if not p.exists():
        return None
    try:
        with open(p, "r", encoding="utf-8") as f:
            if p.suffix == ".lock" and f.read(1) == "{":
                f.seek(0)
                return json.load(f)
            f.seek(0)
            if yaml:
                return yaml.safe_load(f)
            return json.load(f)
    except Exception as e:
        log_warn(f"Lock okunamadı: {e}")
        return None

def save_lock(proj: Project, artifacts: List[Dict[str, str]]):
    data = {
        "lockfileVersion": 1,
        "fcompiler": VERSION,
        "project": f"{proj.group_id}:{proj.name}:{proj.version}",
        "artifacts": sorted(artifacts, key=lambda x: x["key"]),
    }
    p = lock_path(proj)
    with open(p, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
        f.write("\n")
    log_ok(f"Lock yazıldı: {p} ({len(artifacts)} artifact)")

# ── Dependency resolver ────────────────────────────────────
class DependencyResolver:
    def __init__(self, repositories, cache_dir, offline=False, workers=8, lock_data=None,
                 strict_lock=False, conflict_strategy="nearest", prefer=None):
        self.repositories = repositories
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        self.offline = offline
        self.workers = max(1, workers)
        self.lock_data = lock_data
        self.strict_lock = strict_lock
        self.conflict_strategy = conflict_strategy
        self.prefer = prefer or {}
        self._pom_cache: Dict[str, Optional[ET.Element]] = {}
        self.resolved_coords: List[Coord] = []

    def _cache_path(self, coord: Coord, ext: str) -> Path:
        return self.cache_dir / coord.maven_rel(ext)

    def _download(self, url: str, dest: Path) -> bool:
        if self.offline:
            return False
        try:
            log_debug(f"GET {url}")
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=60) as resp:
                data = resp.read()
            dest.parent.mkdir(parents=True, exist_ok=True)
            tmp = dest.with_suffix(dest.suffix + ".tmp")
            tmp.write_bytes(data)
            tmp.replace(dest)
            return True
        except Exception as e:
            log_debug(f"fail {url}: {e}")
            return False

    def fetch_file(self, coord: Coord, ext: str) -> Optional[Path]:
        dest = self._cache_path(coord, ext)
        if dest.exists() and dest.stat().st_size > 0:
            return dest
        if self.offline:
            return None
        rel = coord.maven_rel(ext)
        for repo in self.repositories:
            if self._download(repo.rstrip("/") + "/" + rel, dest):
                return dest
        return None

    def _parse_pom(self, coord: Coord) -> Optional[ET.Element]:
        k = coord.full()
        if k in self._pom_cache:
            return self._pom_cache[k]
        path = self.fetch_file(coord, "pom")
        if not path:
            self._pom_cache[k] = None
            return None
        try:
            root = ET.parse(path).getroot()
            for el in root.iter():
                if "}" in el.tag:
                    el.tag = el.tag.split("}", 1)[1]
            self._pom_cache[k] = root
            return root
        except Exception as e:
            log_debug(f"POM {coord.full()}: {e}")
            self._pom_cache[k] = None
            return None

    def _txt(self, root, path, default=""):
        el = root.find(path)
        return (el.text or "").strip() if el is not None and el.text else default

    def _parent(self, root) -> Optional[Coord]:
        p = root.find("parent")
        if p is None:
            return None
        g, a, v = self._txt(p, "groupId"), self._txt(p, "artifactId"), self._txt(p, "version")
        return Coord(g, a, v) if g and a and v else None

    def _props(self, root, parent_props):
        props = dict(parent_props)
        g = self._txt(root, "groupId") or parent_props.get("project.groupId", "")
        v = self._txt(root, "version") or parent_props.get("project.version", "")
        props.update({"project.groupId": g, "project.artifactId": self._txt(root, "artifactId"),
                      "project.version": v, "groupId": g, "version": v})
        pe = root.find("properties")
        if pe is not None:
            for c in list(pe):
                tag = c.tag.split("}")[-1] if "}" in c.tag else c.tag
                if c.text:
                    props[tag] = c.text.strip()
        return props

    def _interp(self, s, props):
        if not s or "${" not in s:
            return s
        for _ in range(5):
            ns = re.sub(r"\$\{([^}]+)\}", lambda m: props.get(m.group(1), m.group(0)), s)
            if ns == s:
                break
            s = ns
        return s

    def _direct_deps_from_pom(self, coord: Coord) -> List[Dep]:
        root = self._parse_pom(coord)
        if root is None:
            return []
        props, managed = {}, {}
        chain, cur, seen = [], coord, set()
        while cur and cur.full() not in seen:
            seen.add(cur.full())
            r = self._parse_pom(cur)
            if r is None:
                break
            chain.append(r)
            cur = self._parent(r)
        for r in reversed(chain):
            props = self._props(r, props)
            dm = r.find("dependencyManagement")
            if dm is not None and dm.find("dependencies") is not None:
                for d in dm.find("dependencies").findall("dependency"):
                    g = self._interp(self._txt(d, "groupId"), props)
                    a = self._interp(self._txt(d, "artifactId"), props)
                    v = self._interp(self._txt(d, "version"), props)
                    if g and a and v:
                        managed[f"{g}:{a}"] = v
        root, props = chain[0], self._props(chain[0], props)
        result = []
        deps_el = root.find("dependencies")
        if deps_el is None:
            return result
        for d in deps_el.findall("dependency"):
            g = self._interp(self._txt(d, "groupId"), props)
            a = self._interp(self._txt(d, "artifactId"), props)
            v = self._interp(self._txt(d, "version"), props) or managed.get(f"{g}:{a}", "")
            scope = self._interp(self._txt(d, "scope", "compile"), props) or "compile"
            optional = self._txt(d, "optional", "false").lower() == "true"
            typ = self._txt(d, "type", "jar") or "jar"
            if g and a and v and typ in ("jar", ""):
                result.append(Dep(Coord(g, a, v), scope=scope, optional=optional))
        return result

    def resolve(self, direct: List[Dep], scopes=None, include_transitive=True, module_managed=None) -> List[Path]:
        if scopes is None:
            scopes = {"compile", "runtime", ""}
        module_managed = module_managed or {}

        # Strict lock: only use locked artifacts
        if self.strict_lock and self.lock_data and self.lock_data.get("artifacts"):
            jars = []
            for art in self.lock_data["artifacts"]:
                c = Coord(art["group"], art["artifact"], art["version"])
                scope = art.get("scope", "compile")
                if scope not in scopes and scope != "":
                    continue
                p = self.fetch_file(c, "jar")
                if p:
                    jars.append(p)
                    self.resolved_coords.append(c)
                elif art.get("packaging") != "pom":
                    log_err(f"Lock artifact eksik: {c.full()}")
            return sorted(jars, key=lambda x: x.name)

        # Soft lock: pin versions from lock when present
        lock_map = {}
        if self.lock_data and self.lock_data.get("artifacts"):
            for art in self.lock_data["artifacts"]:
                lock_map[f"{art['group']}:{art['artifact']}"] = art["version"]

        queue = deque()
        for d in direct:
            if d.optional:
                continue
            if d.scope not in scopes and d.scope != "":
                continue
            # apply managed / lock pin
            ver = d.coord.version
            ga = d.coord.key()
            if ga in lock_map:
                ver = lock_map[ga]
            elif ga in module_managed and not ver:
                ver = module_managed[ga]
            queue.append((Dep(Coord(d.coord.group, d.coord.artifact, ver), scope=d.scope), 0))

        # Collect all version candidates per GA with depth for conflict mediation
        candidates: Dict[str, List[Tuple[Coord, int]]] = defaultdict(list)
        seen_edge: Set[str] = set()
        while queue:
            dep, depth = queue.popleft()
            ga = dep.coord.key()
            candidates[ga].append((dep.coord, depth))
            edge = f"{dep.coord.full()}@{depth}"
            if edge in seen_edge:
                continue
            seen_edge.add(edge)
            if not include_transitive or dep.scope not in ("compile", "runtime", ""):
                continue
            for td in self._direct_deps_from_pom(dep.coord):
                if td.optional or td.scope in ("test", "provided", "system"):
                    continue
                tga = td.coord.key()
                ver = lock_map.get(tga, td.coord.version)
                if tga in module_managed and tga not in lock_map:
                    ver = module_managed[tga]
                queue.append((Dep(Coord(td.coord.group, td.coord.artifact, ver), scope="compile"), depth + 1))

        def _parse_ver(v: str):
            v = re.sub(r"[-_].*", "", v)
            parts = []
            for p in v.split("."):
                try:
                    parts.append(int(p))
                except ValueError:
                    parts.append(p)
            return tuple(parts)

        strategy = getattr(self, "conflict_strategy", "nearest")
        prefer = getattr(self, "prefer", {}) or {}
        selected: Dict[str, Coord] = {}
        for ga, cands in candidates.items():
            if ga in prefer:
                selected[ga] = Coord(cands[0][0].group, cands[0][0].artifact, prefer[ga])
                continue
            by_ver: Dict[str, Tuple[Coord, int]] = {}
            for c, d in cands:
                if c.version not in by_ver or d < by_ver[c.version][1]:
                    by_ver[c.version] = (c, d)
            items = list(by_ver.values())
            if len(items) == 1:
                selected[ga] = items[0][0]
                continue
            msg = f"Çakışma {ga}: " + ", ".join(f"{c.version}@d{d}" for c, d in items)
            if strategy == "fail":
                log_err(msg + " [fail]")
                return []
            if strategy == "newest":
                best = max(items, key=lambda x: _parse_ver(x[0].version))
                log_warn(msg + f" → newest={best[0].version}")
                selected[ga] = best[0]
            else:
                best = min(items, key=lambda x: (x[1], x[0].version))
                log_warn(msg + f" → nearest={best[0].version}")
                selected[ga] = best[0]

        coords = list(selected.values())
        self.resolved_coords = coords
        jars = []

        def fetch_one(c: Coord):
            p = self.fetch_file(c, "jar")
            if p:
                return p
            pom = self._parse_pom(c)
            if pom is not None and self._txt(pom, "packaging", "jar") == "pom":
                return None
            return None

        with concurrent.futures.ThreadPoolExecutor(max_workers=self.workers) as ex:
            futs = {ex.submit(fetch_one, c): c for c in coords}
            for fut in concurrent.futures.as_completed(futs):
                c = futs[fut]
                try:
                    path = fut.result()
                    if path:
                        jars.append(path)
                        log_info(f"  ✓ {c.full()}")
                except Exception as e:
                    log_err(f"{c.full()}: {e}")
        return sorted(jars, key=lambda p: p.name)

    def resolve_test(self, direct, module_managed=None):
        return self.resolve(direct, scopes={"compile", "runtime", "test", ""}, include_transitive=True, module_managed=module_managed)

# ── Compiler / Jar / Test (same as v3, condensed) ───────────
class Compiler:
    def __init__(self, mod: ModuleConfig):
        self.mod = mod

    @staticmethod
    @staticmethod
    def check_jdk(preferred: str = "17"):
        return ensure_jdk(preferred)

    def _java_files(self, src):
        return sorted(src.rglob("*.java")) if src.exists() else []

    def _stale(self, files, src_root, out_root):
        stale = []
        for jf in files:
            cf = out_root / jf.relative_to(src_root).with_suffix(".class")
            if not cf.exists() or jf.stat().st_mtime > cf.stat().st_mtime:
                stale.append(jf)
        return stale

    def _copy_res(self, res_dir, dest):
        if not res_dir.exists():
            return
        for f in res_dir.rglob("*"):
            if f.is_file():
                t = dest / f.relative_to(res_dir)
                t.parent.mkdir(parents=True, exist_ok=True)
                if not t.exists() or f.stat().st_mtime > t.stat().st_mtime:
                    shutil.copy2(f, t)

    def compile_sources(self, src_dir, out_dir, classpath, force=False, label="main"):
        files = self._java_files(src_dir)
        if not files:
            if label == "main":
                log_err(f"Kaynak yok: {src_dir}")
                return False
            log_info(f"Test kaynağı yok, atlanıyor.")
            return True
        stale = files if force else self._stale(files, src_dir, out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
        self._copy_res(self.mod.resources_dir if label == "main" else self.mod.test_resources_dir, out_dir)
        if not stale:
            log_info(f"[{self.mod.name}] {label}: güncel (incremental, {len(files)} dosya)")
            return True
        log_step(f"[{self.mod.name}] {label}: {len(stale)}/{len(files)} dosya...")
        cmd = [_javac_cmd, "-d", str(out_dir), "-source", self.mod.java_version,
               "-target", self.mod.java_version, "-encoding", self.mod.encoding]
        if self.mod.debug:
            cmd.append("-g")
        cps = os.pathsep.join(str(p) for p in ([out_dir] + list(classpath)) if p)
        if cps:
            cmd.extend(["-cp", cps])
        # Annotation processors
        proc_path = getattr(self, "_processor_path", None)
        if label == "main" and (getattr(self.mod, "annotation_processors", None) or proc_path):
            if proc_path:
                cmd.extend(["-processorpath", os.pathsep.join(str(p) for p in proc_path)])
            procs = getattr(self.mod, "annotation_processors", None) or []
            if procs:
                cmd.extend(["-processor", ",".join(procs)])
            gen = self.mod.build_dir / "generated-sources" / "annotations"
            gen.mkdir(parents=True, exist_ok=True)
            cmd.extend(["-s", str(gen)])
        cmd.extend(str(f) for f in files)
        t0 = time.time()
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode != 0:
            log_err(f"[{self.mod.name}] derleme hatası:")
            print(r.stderr or r.stdout or "")
            return False
        log_ok(f"[{self.mod.name}] {label} ({time.time()-t0:.2f}s)")
        return True

    def compile_main(self, dep_jars, module_jars, force=False, processor_jars=None):
        self._processor_path = processor_jars
        return self.compile_sources(self.mod.src_dir, self.mod.classes_dir, module_jars + dep_jars, force, "main")

    def compile_tests(self, dep_jars, module_jars, force=False):
        self._processor_path = None
        return self.compile_sources(self.mod.test_src_dir, self.mod.test_classes_dir,
                                    [self.mod.classes_dir] + module_jars + dep_jars, force, "test")

class JarPackager:
    def __init__(self, mod): self.mod = mod

    def _manifest(self, fat):
        lines = ["Manifest-Version: 1.0", f"Created-By: FCompiler {VERSION}",
                 f"Implementation-Title: {self.mod.name}", f"Implementation-Version: {self.mod.version}"]
        if self.mod.main_class:
            lines.append(f"Main-Class: {self.mod.main_class}")
        if not fat and self.mod.lib_dir.exists():
            libs = sorted(self.mod.lib_dir.glob("*.jar"))
            if libs:
                lines.append("Class-Path: " + " ".join(f"libs/{p.name}" for p in libs))
        return "\n".join(lines) + "\n\n"

    def _add(self, zf, root):
        if root.exists():
            for f in root.rglob("*"):
                if f.is_file():
                    zf.write(f, f.relative_to(root).as_posix())

    def package_thin(self, dep_jars):
        log_step(f"[{self.mod.name}] thin JAR...")
        self.mod.jar_dir.mkdir(parents=True, exist_ok=True)
        self.mod.lib_dir.mkdir(parents=True, exist_ok=True)
        for j in dep_jars:
            dest = self.mod.lib_dir / j.name
            if not dest.exists() or dest.stat().st_mtime < j.stat().st_mtime:
                shutil.copy2(j, dest)
        path = self.mod.jar_dir / self.mod.jar_name
        with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as zf:
            zf.writestr("META-INF/MANIFEST.MF", self._manifest(False))
            self._add(zf, self.mod.classes_dir)
        log_ok(f"[{self.mod.name}] {path.name}")
        return path

    def package_fat(self, dep_jars):
        log_step(f"[{self.mod.name}] fat JAR...")
        self.mod.jar_dir.mkdir(parents=True, exist_ok=True)
        path = self.mod.jar_dir / self.mod.fat_jar_name
        with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as zf:
            zf.writestr("META-INF/MANIFEST.MF", self._manifest(True))
            self._add(zf, self.mod.classes_dir)
            seen = set(zf.namelist())
            for dep in dep_jars:
                with zipfile.ZipFile(dep, "r") as dz:
                    for item in dz.namelist():
                        if item.endswith("/") or item in seen:
                            continue
                        if item.startswith("META-INF/") and (item.endswith((".SF", ".RSA", ".DSA")) or item == "META-INF/MANIFEST.MF" or "SIG-" in item):
                            continue
                        zf.writestr(item, dz.read(item))
                        seen.add(item)
        log_ok(f"[{self.mod.name}] {path.name}")
        return path

def run_tests(mod, classpath):
    if not mod.test_classes_dir.exists():
        log_info(f"[{mod.name}] test yok")
        return True
    cp = os.pathsep.join([str(mod.test_classes_dir), str(mod.classes_dir)] + [str(p) for p in classpath])
    if any("junit-platform-console" in p.name for p in classpath):
        cmd = [_java_cmd, "-cp", cp, "org.junit.platform.console.ConsoleLauncher",
               "--scan-class-path", str(mod.test_classes_dir), "--details=tree"]
        log_step(f"[{mod.name}] JUnit Platform...")
        r = subprocess.run(cmd, capture_output=True, text=True)
        print(r.stdout or "")
        if r.returncode == 0:
            log_ok(f"[{mod.name}] testler geçti")
            return True
        if "ClassNotFoundException" not in (r.stderr or "") and "Could not find or load" not in (r.stderr or ""):
            print(r.stderr or "")
            return False
    tests = [f.relative_to(mod.test_classes_dir).with_suffix("").as_posix().replace("/", ".")
             for f in mod.test_classes_dir.rglob("*Test.class") if "$" not in f.name]
    if not tests:
        log_info(f"[{mod.name}] *Test.class yok")
        return True
    failed = 0
    for tc in tests:
        r = subprocess.run([_java_cmd, "-cp", cp, tc], capture_output=True, text=True)
        if r.returncode != 0:
            failed += 1
            log_err(f"FAIL {tc}")
            print(r.stdout or "", r.stderr or "")
        else:
            log_ok(f"PASS {tc}")
    return failed == 0

# ── Build orchestration ────────────────────────────────────
def _resolver(proj, offline, workers, strict_lock=False):
    return DependencyResolver(
        proj.repositories, proj.root / ".fcompiler" / "cache",
        offline=offline, workers=workers,
        lock_data=load_lock(proj), strict_lock=strict_lock,
    )

def build_module(mod, proj, built_jars, offline, force, do_package, fat, workers, api: PluginAPI, strict_lock=False):
    api.module = mod
    if not api.emit("before_build", module=mod):
        return False
    log_step(f"Modül: {mod.name}")
    module_jars = []
    for md in mod.module_deps:
        if md not in built_jars:
            log_err(f"Modül sırası: {mod.name} → {md}")
            return False
        module_jars.append(built_jars[md])
    if not api.emit("before_resolve", module=mod):
        return False
    r = _resolver(proj, offline, workers, strict_lock)
    r.conflict_strategy = getattr(mod, "conflict_strategy", "nearest")
    r.prefer = getattr(mod, "prefer", {}) or {}
    jars = r.resolve(mod.deps, module_managed=mod.managed)
    proc_jars = []
    if getattr(mod, "processor_path_deps", None):
        proc_jars = r.resolve(mod.processor_path_deps, module_managed=mod.managed)
    if not api.emit("after_resolve", module=mod, jars=jars, coords=r.resolved_coords):
        return False
    if not api.emit("before_compile", module=mod):
        return False
    if not Compiler(mod).compile_main(jars, module_jars, force=force, processor_jars=proc_jars or None):
        return False
    if not api.emit("after_compile", module=mod):
        return False
    if do_package:
        if not api.emit("before_package", module=mod):
            return False
        pack = JarPackager(mod)
        thin = pack.package_thin(jars + module_jars)
        if fat:
            pack.package_fat(jars + module_jars)
        if thin:
            built_jars[mod.name] = thin
        if not api.emit("after_package", module=mod, jar=thin):
            return False
    if not api.emit("after_build", module=mod):
        return False
    return True

def test_module(mod, proj, built_jars, offline, force, workers, api):
    api.module = mod
    if not api.emit("before_test", module=mod):
        return False
    r = _resolver(proj, offline, workers)
    module_jars = [built_jars[m] for m in mod.module_deps if m in built_jars]
    jars = r.resolve_test(mod.deps, module_managed=mod.managed)
    main_jars = r.resolve(mod.deps, module_managed=mod.managed)
    comp = Compiler(mod)
    if not comp.compile_main(main_jars, module_jars, force=force):
        return False
    if not comp.compile_tests(jars, module_jars, force=force):
        return False
    ok = run_tests(mod, jars + module_jars)
    if not api.emit("after_test", module=mod, success=ok):
        return False
    return ok

# ── IDE integration ────────────────────────────────────────
def ide_eclipse(proj: Project):
    for mod in proj.modules:
        src = mod.src_dir.relative_to(mod.root).as_posix() if mod.src_dir.exists() else "src"
        # .project
        (mod.root / ".project").write_text(f'''<?xml version="1.0" encoding="UTF-8"?>
<projectDescription>
  <name>{mod.name}</name>
  <comment>FCompiler</comment>
  <buildSpec>
    <buildCommand><name>org.eclipse.jdt.core.javabuilder</name><arguments/></buildCommand>
  </buildSpec>
  <natures>
    <nature>org.eclipse.jdt.core.javanature</nature>
  </natures>
</projectDescription>
''', encoding="utf-8")
        # .classpath
        entries = [
            f'  <classpathentry kind="src" path="{src}"/>',
            '  <classpathentry kind="con" path="org.eclipse.jdt.launching.JRE_CONTAINER"/>',
            '  <classpathentry kind="output" path="build/classes"/>',
        ]
        lib = mod.lib_dir
        if lib.exists():
            for j in sorted(lib.glob("*.jar")):
                rel = j.relative_to(mod.root).as_posix()
                entries.append(f'  <classpathentry kind="lib" path="{rel}"/>')
        # also cache jars from resolver if libs empty
        cache = proj.root / ".fcompiler" / "cache"
        if cache.exists() and not (lib.exists() and any(lib.glob("*.jar"))):
            for j in cache.rglob("*.jar"):
                entries.append(f'  <classpathentry kind="lib" path="{j.as_posix()}"/>')
        (mod.root / ".classpath").write_text(
            '<?xml version="1.0" encoding="UTF-8"?>\n<classpath>\n' + "\n".join(entries) + "\n</classpath>\n",
            encoding="utf-8",
        )
        log_ok(f"Eclipse: {mod.root}/.project + .classpath")

def ide_idea(proj: Project):
    idea = proj.root / ".idea"
    idea.mkdir(exist_ok=True)
    (idea / "misc.xml").write_text(f'''<?xml version="1.0" encoding="UTF-8"?>
<project version="4">
  <component name="ProjectRootManager" version="2" languageLevel="JDK_{proj.modules[0].java_version}" />
</project>
''', encoding="utf-8")
    modules_xml = ['<?xml version="1.0" encoding="UTF-8"?>', '<project version="4">',
                   '  <component name="ProjectModuleManager">', '    <modules>']
    for mod in proj.modules:
        iml = mod.root / f"{mod.name}.iml"
        src = mod.src_dir.relative_to(mod.root).as_posix() if mod.src_dir.is_relative_to(mod.root) else "src"
        lib_entries = ""
        if mod.lib_dir.exists():
            for j in sorted(mod.lib_dir.glob("*.jar")):
                lib_entries += f'''
      <orderEntry type="module-library">
        <library><CLASSES><root url="jar://$MODULE_DIR$/{j.relative_to(mod.root).as_posix()}!/"/></CLASSES></library>
      </orderEntry>'''
        iml.write_text(f'''<?xml version="1.0" encoding="UTF-8"?>
<module type="JAVA_MODULE" version="4">
  <component name="NewModuleRootManager" inherit-compiler-output="true">
    <exclude-output />
    <content url="file://$MODULE_DIR$">
      <sourceFolder url="file://$MODULE_DIR$/{src}" isTestSource="false" />
    </content>
    <orderEntry type="inheritedJdk" />
    <orderEntry type="sourceFolder" forTests="false" />{lib_entries}
  </component>
</module>
''', encoding="utf-8")
        rel = iml.relative_to(proj.root).as_posix()
        modules_xml.append(f'      <module fileurl="file://$PROJECT_DIR$/{rel}" filepath="$PROJECT_DIR$/{rel}" />')
        log_ok(f"IntelliJ: {iml}")
    modules_xml += ["    </modules>", "  </component>", "</project>"]
    (idea / "modules.xml").write_text("\n".join(modules_xml) + "\n", encoding="utf-8")
    log_ok(f"IntelliJ: {idea}/modules.xml")

def ide_vscode(proj: Project):
    vscode = proj.root / ".vscode"
    vscode.mkdir(exist_ok=True)
    # settings
    settings = {
        "java.configuration.updateBuildConfiguration": "automatic",
        "java.project.sourcePaths": [],
        "java.project.outputPath": "build/classes",
        "java.project.referencedLibraries": ["build/libs/**/*.jar", ".fcompiler/cache/**/*.jar"],
    }
    for mod in proj.modules:
        try:
            rel = str(mod.src_dir.relative_to(proj.root)).replace("\\", "/")
        except ValueError:
            rel = str(mod.src_dir)
        settings["java.project.sourcePaths"].append(rel)
    (vscode / "settings.json").write_text(json.dumps(settings, indent=2) + "\n", encoding="utf-8")
    # launch.json for main classes
    configs = []
    for mod in proj.modules:
        if mod.main_class:
            fat = mod.jar_dir / mod.fat_jar_name
            configs.append({
                "type": "java",
                "name": f"Run {mod.name}",
                "request": "launch",
                "mainClass": mod.main_class,
                "projectName": mod.name,
                "classPaths": [str(mod.classes_dir), str(mod.lib_dir / "*")],
            })
    if configs:
        (vscode / "launch.json").write_text(json.dumps({"version": "0.2.0", "configurations": configs}, indent=2) + "\n", encoding="utf-8")
    # tasks.json
    tasks = {
        "version": "2.0.0",
        "tasks": [
            {"label": "fcompiler: build", "type": "shell", "command": f"{sys.executable} fcompiler.py build",
             "group": {"kind": "build", "isDefault": True}, "problemMatcher": []},
            {"label": "fcompiler: test", "type": "shell", "command": f"{sys.executable} fcompiler.py test",
             "group": "test", "problemMatcher": []},
            {"label": "fcompiler: clean", "type": "shell", "command": f"{sys.executable} fcompiler.py clean", "problemMatcher": []},
        ],
    }
    # prefer local script name
    fc = "fcompiler.py" if (proj.root / "fcompiler.py").exists() else "python fcompiler.py"
    for t in tasks["tasks"]:
        t["command"] = t["command"].replace(f"{sys.executable} fcompiler.py", f"{sys.executable} " + (
            str(Path(sys.argv[0]).resolve()) if "fcompiler" in sys.argv[0] else "fcompiler.py"
        ))
    (vscode / "tasks.json").write_text(json.dumps(tasks, indent=2) + "\n", encoding="utf-8")
    log_ok(f"VS Code: {vscode}/settings.json, launch.json, tasks.json")

# ── CLI ────────────────────────────────────────────────────
def cmd_init(args):
    base = Path(args.directory or ".").resolve()
    g = args.group
    if args.multi:
        root = base / (args.name or "multi-app")
        root.mkdir(parents=True, exist_ok=True)
        (root / "projectinfo.toml").write_text(f'''[project]
name = "{root.name}"
version = "1.0.0"
groupId = "{g}"

[modules]
list = ["core", "app"]

[repositories]
urls = ["https://repo1.maven.org/maven2/"]
''', encoding="utf-8")
        (root / ".fcompiler" / "plugins").mkdir(parents=True, exist_ok=True)
        (root / ".fcompiler" / "plugins" / "example_plugin.py").write_text('''# FCompiler plugin örneği
def register(api):
    def on_after_build(api, **ctx):
        api  # PluginAPI
        mod = ctx.get("module")
        print(f"[example_plugin] build bitti: {mod.name if mod else "?"}")
    api.on("after_build", on_after_build)
''', encoding="utf-8")
        for mname, main in [("core", None), ("app", f"{g}.app.Main")]:
            mroot = root / mname
            mroot.mkdir(parents=True, exist_ok=True)
            deps = 'dependsOn = ["core"]' if mname == "app" else ""
            (mroot / "projectinfo.toml").write_text(f'''[project]
name = "{mname}"
version = "1.0.0"
groupId = "{g}"
{f'mainClass = "{main}"' if main else ""}
javaVersion = "17"
[build]
sourceDir = "src"
outputDir = "build"
[modules]
{deps}
''', encoding="utf-8")
            (mroot / "dependencies.yml").write_text("dependencies: []\n", encoding="utf-8")
            if mname == "core":
                d = mroot / "src" / g.replace(".", "/") / "core"
                d.mkdir(parents=True, exist_ok=True)
                (d / "Lib.java").write_text(f"package {g}.core;\npublic class Lib {{\n  public static String hello() {{ return \"core-ok\"; }}\n}}\n", encoding="utf-8")
            else:
                d = mroot / "src" / g.replace(".", "/") / "app"
                d.mkdir(parents=True, exist_ok=True)
                (d / "Main.java").write_text(f"package {g}.app;\nimport {g}.core.Lib;\npublic class Main {{\n  public static void main(String[] a) {{\n    System.out.println(Lib.hello());\n  }}\n}}\n", encoding="utf-8")
        log_ok(f"Multi-module + örnek plugin: {root}")
        return
    name = args.name
    root = (base / name) if name else base
    if name:
        root.mkdir(parents=True, exist_ok=True)
    main = args.main or f"{g}.Main"
    (root / "projectinfo.toml").write_text(f'''[project]
name = "{root.name}"
version = "{args.version}"
groupId = "{g}"
mainClass = "{main}"
javaVersion = "17"
encoding = "UTF-8"

[build]
sourceDir = "src"
testSourceDir = "src/test/java"
resourcesDir = "resources"
outputDir = "build"

# BOM / version management
[dependencyManagement]
# dependencies = [ "com.google.code.gson:gson:2.10.1" ]

[repositories]
urls = ["https://repo1.maven.org/maven2/"]
''', encoding="utf-8")
    (root / "dependencies.yml").write_text('''# dependencies:
#   - "com.google.code.gson:gson:2.10.1"
#   - groupId: org.junit.jupiter
#     artifactId: junit-jupiter
#     version: "5.10.2"
#     scope: test
dependencies: []
''', encoding="utf-8")
    pkg, cls = main.rsplit(".", 1)[0].replace(".", "/"), main.rsplit(".", 1)[-1]
    sd = root / "src" / pkg
    sd.mkdir(parents=True, exist_ok=True)
    (root / "resources").mkdir(exist_ok=True)
    (root / "src" / "test" / "java").mkdir(parents=True, exist_ok=True)
    (root / ".fcompiler" / "plugins").mkdir(parents=True, exist_ok=True)
    (sd / f"{cls}.java").write_text(f"package {main.rsplit('.',1)[0]};\npublic class {cls} {{\n  public static void main(String[] args) {{\n    System.out.println(\"Hello FCompiler {VERSION}\");\n  }}\n}}\n", encoding="utf-8")
    (root / ".fcompiler" / "plugins" / "example_plugin.py").write_text(
        'def register(api):\n    api.on("after_build", lambda api, **ctx: print("[plugin] after_build"))\n',
        encoding="utf-8",
    )
    (root / ".gitignore").write_text("build/\n.fcompiler/cache/\n*.class\n*.jar\n.idea/\n.vscode/\n.classpath\n.project\n*.iml\n", encoding="utf-8")
    log_ok(f"Proje: {root}")

def cmd_lock(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    artifacts = []
    seen = set()
    for mod in topological_modules(proj.modules):
        r = DependencyResolver(proj.repositories, proj.root / ".fcompiler" / "cache",
                               offline=args.offline, workers=args.jobs)
        r.resolve(mod.deps, scopes={"compile", "runtime", "test", ""}, module_managed=mod.managed)
        for c in r.resolved_coords:
            if c.full() in seen:
                continue
            seen.add(c.full())
            artifacts.append({"key": c.key(), "group": c.group, "artifact": c.artifact, "version": c.version, "scope": "compile"})
    save_lock(proj, artifacts)

def cmd_clean(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        return
    for m in proj.modules:
        if m.build_dir.exists():
            shutil.rmtree(m.build_dir)
            log_ok(f"Silindi {m.build_dir}")
    if args.all:
        c = proj.root / ".fcompiler" / "cache"
        if c.exists():
            shutil.rmtree(c)
            log_ok(f"Silindi {c}")

def cmd_deps(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    for mod in proj.modules:
        log_step(f"deps: {mod.name}")
        r = _resolver(proj, args.offline, args.jobs, strict_lock=args.strict_lock)
        jars = r.resolve(mod.deps, module_managed=mod.managed)
        log_ok(f"{mod.name}: {len(jars)} jar")
        for j in jars:
            print(f"  • {j.name}")

def cmd_tree(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    for mod in proj.modules:
        print(f"{mod.group_id}:{mod.name}:{mod.version}")
        for md in mod.module_deps:
            print(f"├── [module] {md}")
        for d in mod.deps:
            print(f"├── {d.coord.full()} [{d.scope}]")
        r = _resolver(proj, args.offline, args.jobs)
        jars = r.resolve(mod.deps, module_managed=mod.managed)
        print(f"└── resolved: {len(jars)}")
        for j in jars[:40]:
            print(f"    • {j.name}")

def cmd_compile(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    ok, ver = Compiler.check_jdk()
    if not ok:
        log_err(ver); sys.exit(1)
    log_info(ver)
    api = load_plugins(proj)
    built = {}
    for mod in topological_modules(proj.modules):
        if not build_module(mod, proj, built, args.offline, args.force, True, False, args.jobs, api, args.strict_lock):
            sys.exit(1)

def cmd_package(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    ok, ver = Compiler.check_jdk()
    if not ok:
        log_err(ver); sys.exit(1)
    api = load_plugins(proj)
    built = {}
    for mod in topological_modules(proj.modules):
        if not build_module(mod, proj, built, args.offline, args.force, True, args.fat, args.jobs, api, args.strict_lock):
            sys.exit(1)

def cmd_build(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    log_step(f"Build {proj.name}" + (" [multi]" if proj.is_multi else ""))
    ok, ver = Compiler.check_jdk()
    if not ok:
        log_err(ver); sys.exit(1)
    log_info(ver)
    api = load_plugins(proj)
    built = {}
    t0 = time.time()
    for mod in topological_modules(proj.modules):
        if not build_module(mod, proj, built, args.offline, args.force, True, True, args.jobs, api, args.strict_lock):
            sys.exit(1)
    log_ok(f"Build tamam ({time.time()-t0:.2f}s)")

def cmd_test(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    ok, ver = Compiler.check_jdk()
    if not ok:
        log_err(ver); sys.exit(1)
    api = load_plugins(proj)
    built = {}
    for mod in topological_modules(proj.modules):
        if not build_module(mod, proj, built, args.offline, args.force, True, False, args.jobs, api, args.strict_lock):
            sys.exit(1)
    failed = False
    for mod in topological_modules(proj.modules):
        if not test_module(mod, proj, built, args.offline, args.force, args.jobs, api):
            failed = True
    if failed:
        sys.exit(1)
    log_ok("Testler geçti")

def cmd_run(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    target = None
    for m in reversed(topological_modules(proj.modules)):
        if m.main_class:
            target = m
            break
    if not target:
        log_err("mainClass yok"); sys.exit(1)
    fat, thin = target.jar_dir / target.fat_jar_name, target.jar_dir / target.jar_name
    if not fat.exists() and not thin.exists():
        class A: directory=args.directory; offline=args.offline; force=False; jobs=args.jobs; strict_lock=False
        cmd_build(A())
    if fat.exists():
        cmd = [_java_cmd, "-jar", str(fat)] + list(args.args or [])
    else:
        cp = [str(thin)] + ([str(p) for p in target.lib_dir.glob("*.jar")] if target.lib_dir.exists() else [])
        cmd = [_java_cmd, "-cp", os.pathsep.join(cp), target.main_class] + list(args.args or [])
    log_step(" ".join(cmd))
    print("─" * 50)
    sys.stdout.flush()
    sys.exit(subprocess.run(cmd).returncode)

def cmd_ide(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    # ensure deps resolved so libs exist
    for mod in proj.modules:
        r = _resolver(proj, args.offline, args.jobs)
        jars = r.resolve(mod.deps, module_managed=mod.managed)
        mod.lib_dir.mkdir(parents=True, exist_ok=True)
        for j in jars:
            dest = mod.lib_dir / j.name
            if not dest.exists():
                shutil.copy2(j, dest)
    target = (args.target or "all").lower()
    if target in ("eclipse", "all"):
        ide_eclipse(proj)
    if target in ("idea", "intellij", "all"):
        ide_idea(proj)
    if target in ("vscode", "code", "all"):
        ide_vscode(proj)
    log_ok("IDE dosyaları hazır")

def cmd_info(args):
    proj = load_project(Path(args.directory or "."))
    if not proj:
        sys.exit(1)
    print(_col(_C.Bold, f"FCompiler {VERSION}"))
    print(f"  {proj.name} {proj.version} multi={proj.is_multi}")
    lock = load_lock(proj)
    print(f"  lockfile: {'var ('+str(len(lock.get('artifacts',[])))+' art)' if lock else 'yok'}")
    for m in topological_modules(proj.modules):
        print(f"  • {m.name} main={m.main_class or '-'} deps={len(m.deps)}")

def cmd_doctor(args):
    print(_col(_C.Bold, f"Doctor {VERSION}"))
    print(f"  Python: {sys.version.split()[0]}")
    ok, ver = Compiler.check_jdk()
    print(f"  javac: {ver}")
    print(f"  tomllib: {'OK' if tomllib else 'EKSIK'}  yaml: {'OK' if yaml else 'EKSIK'}")

def cmd_version(args):
    print(f"FCompiler {VERSION}")

def main():
    global _quiet, _verbose, _no_color
    parser = argparse.ArgumentParser(prog="fcompiler", description=f"FCompiler {VERSION}")
    parser.add_argument("-d", "--directory", default=".")
    parser.add_argument("-q", "--quiet", action="store_true")
    parser.add_argument("-v", "--verbose", action="store_true")
    parser.add_argument("--no-color", action="store_true")
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--strict-lock", action="store_true", help="Sadece lock dosyasındaki sürümler")
    parser.add_argument("-j", "--jobs", type=int, default=8)
    sub = parser.add_subparsers(dest="command")
    p = sub.add_parser("init"); p.add_argument("name", nargs="?"); p.add_argument("--group", default="com.example"); p.add_argument("--version", default="1.0.0"); p.add_argument("--main"); p.add_argument("--multi", action="store_true"); p.set_defaults(func=cmd_init)
    p = sub.add_parser("lock", help="dependencies.lock üret"); p.set_defaults(func=cmd_lock)
    p = sub.add_parser("clean"); p.add_argument("--all", action="store_true"); p.set_defaults(func=cmd_clean)
    p = sub.add_parser("deps"); p.set_defaults(func=cmd_deps)
    p = sub.add_parser("tree"); p.set_defaults(func=cmd_tree)
    p = sub.add_parser("compile"); p.set_defaults(func=cmd_compile)
    p = sub.add_parser("package"); p.add_argument("--fat", action="store_true"); p.set_defaults(func=cmd_package)
    p = sub.add_parser("build"); p.set_defaults(func=cmd_build)
    p = sub.add_parser("test"); p.set_defaults(func=cmd_test)
    p = sub.add_parser("run"); p.add_argument("args", nargs="*"); p.set_defaults(func=cmd_run)
    p = sub.add_parser("ide", help="IDE proje dosyaları"); p.add_argument("target", nargs="?", default="all", help="eclipse|idea|vscode|all"); p.set_defaults(func=cmd_ide)
    p = sub.add_parser("info"); p.set_defaults(func=cmd_info)
    p = sub.add_parser("doctor"); p.set_defaults(func=cmd_doctor)
    p = sub.add_parser("version"); p.set_defaults(func=cmd_version)
    args = parser.parse_args()
    _quiet, _verbose, _no_color = args.quiet, args.verbose, args.no_color
    if not args.command:
        parser.print_help(); sys.exit(0)
    if not hasattr(args, "strict_lock"):
        args.strict_lock = False
    args.func(args)

if __name__ == "__main__":
    main()
