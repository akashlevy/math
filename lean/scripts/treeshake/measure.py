#!/usr/bin/env python3
"""Size of the local (non-Mathlib) import closure of a module.

Reports modules, total lines, non-blank non-comment lines, import/open lines, and
non-whitespace characters, so that line-format changes cannot masquerade as savings.

Usage: python3 scripts/measure.py MODULE [MODULE ...]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from importgraph import closure, module_path  # noqa: E402


def strip_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else "")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def measure(roots: list[str]) -> dict:
    mods, _ = closure(roots)
    tot = code = hdr = chars = 0
    for m in mods:
        text = module_path(m).read_text()
        tot += len(text.splitlines())
        body = strip_comments(text)
        for line in body.splitlines():
            s = line.strip()
            if not s:
                continue
            code += 1
            if re.match(r"(import|open)\b", s):
                hdr += 1
        chars += len(re.sub(r"\s", "", body))
    return {"modules": len(mods), "lines": tot, "code_lines": code,
            "import_open_lines": hdr, "nonws_chars": chars}


if __name__ == "__main__":
    r = measure(sys.argv[1:])
    print("  ".join(f"{k}={v}" for k, v in r.items()))
