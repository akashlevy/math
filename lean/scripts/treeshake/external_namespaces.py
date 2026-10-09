#!/usr/bin/env python3
"""List every namespace registered outside the local library (Mathlib and other dependencies).

treeshake.py --external-namespaces uses this list to decide whether an `open X` still resolves after
pruning: an atom is only dropped if no surviving namespace, local or external, is named by it.

Usage (from lean/): python3 scripts/treeshake/external_namespaces.py ROOT_MODULE ... --out FILE
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from importgraph import ROOT, closure  # noqa: E402

TEMPLATE = r'''{imports}
open Lean Elab Command

elab "#dump_namespaces" : command => do
  let env ← getEnv
  let mut out : Array String := #[]
  for n in env.getNamespaces do
    out := out.push s!"{{n}}"
  IO.FS.writeFile "{out}" (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"namespaces: {{out.size}}"

#dump_namespaces
'''


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("roots", nargs="+", help="root modules whose external imports to load")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    _, external = closure(a.roots)
    src = TEMPLATE.format(imports="\n".join(f"import {m}" for m in sorted(external)),
                          out=str(Path(a.out).resolve()))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=os.environ.get("TMPDIR")) as f:
        f.write(src)
        path = f.name
    r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True)
    os.unlink(path)
    print((r.stdout + r.stderr).strip())
    return r.returncode


if __name__ == "__main__":
    sys.exit(main())
