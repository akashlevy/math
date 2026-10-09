"""Import-graph utilities over the Lean sources of this library (run from `lean/`)."""
from __future__ import annotations
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]  # the lean/ directory
SRC_DIRS = [ROOT]  # module name -> path resolution order
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»']+)", re.M)


def module_path(mod: str) -> Path | None:
    rel = Path(*mod.split(".")).with_suffix(".lean")
    for d in SRC_DIRS:
        p = d / rel
        if p.is_file():
            return p
    return None


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def header_imports(path: Path) -> list[str]:
    text = strip_comments(path.read_text())
    # imports must precede the first non-import command; scan the header only
    out = []
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("module") or s.startswith("prelude"):
            continue
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
        else:
            break
    return out


_cache: dict[str, list[str]] = {}


def local_imports(mod: str) -> list[str]:
    if mod not in _cache:
        p = module_path(mod)
        _cache[mod] = header_imports(p) if p else []
    return _cache[mod]


def is_local(mod: str) -> bool:
    return module_path(mod) is not None


def closure(roots: list[str]) -> tuple[set[str], set[str]]:
    """Return (local modules, external import names) reachable from roots (roots included)."""
    seen: set[str] = set()
    external: set[str] = set()
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        if not is_local(m):
            external.add(m)
            continue
        seen.add(m)
        stack.extend(local_imports(m))
    return seen, external

