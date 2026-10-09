#!/usr/bin/env python3
"""Exact declaration reachability from a root theorem, computed inside Lean.

Writes a TSV with one row per declaration that has a source range:
    module  name  start_line  end_line  reachable(0/1)  statement_closed(0/1)  rfl_theorem(0/1)
Reachability follows every constant mentioned in types, values (proof terms) and
inductive structure, starting from the given root constant(s).

Usage: python3 scripts/reach.py --import MOD [--import MOD ...] --root CONST [--root CONST ...]
           [--root-module-prefix MODPREFIX ...] [--cwd WORKSPACE] --prefix OAI --out FILE
--root-module-prefix makes every constant declared in a module under MODPREFIX a root (used for
modules that other libraries import, whose whole API must survive).
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]  # the lean/ directory

TEMPLATE = r'''{imports}
open Lean Elab Command

def directDeps (ci : ConstantInfo) : Array Name := Id.run do
  let mut cs := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
  match ci with
  | .inductInfo i => cs := cs ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo c => cs := cs.push c.induct
  | .recInfo r => cs := cs ++ r.all.toArray
  | _ => pure ()
  return cs

def reach (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {{}}
  let mut stack := roots
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in directDeps ci do
        if !seen.contains c then stack := stack.push c
  return seen

elab "#reach_tsv" : command => liftTermElabM do
  let env ← getEnv
  let mut roots : Array Name := #[{roots}]
  let modPrefixes : Array Name := #[{modprefixes}]
  if modPrefixes.size > 0 then
    for (n, _) in env.constants.toList do
      let some idx := env.getModuleIdxFor? n | continue
      let mod := env.header.moduleNames[idx.toNat]!
      if modPrefixes.any (·.isPrefixOf mod) then roots := roots.push n
  let used := reach env roots
  let mut rows : Array String := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.getRoot == `{prefix} do continue
    let some rg ← findDeclarationRanges? n | continue
    let u := if used.contains n then 1 else 0
    -- 1 iff every constant in the statement is reachable (or lives outside {prefix})
    let closed := (env.find? n).get!.type.getUsedConstants.all fun c =>
      used.contains c || (match env.getModuleIdxFor? c with
        | some i => env.header.moduleNames[i.toNat]!.getRoot != `{prefix}
        | none => true)
    let tc := if closed then 1 else 0
    -- rfl theorems can be used by simp/dsimp by unfolding, leaving no trace in proof terms
    let isRfl ← (Meta.isRflTheorem n : MetaM Bool)
    let rf := if isRfl then 1 else 0
    rows := rows.push s!"{{mod}}\t{{n}}\t{{rg.range.pos.line}}\t{{rg.range.endPos.line}}\t{{u}}\t{{tc}}\t{{rf}}"
  IO.FS.writeFile "{out}" (String.intercalate "\n" rows.toList ++ "\n")
  logInfo m!"declarations with ranges: {{rows.size}}; reachable constants: {{used.size}}"

#reach_tsv
'''


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--import", dest="imp", action="append", required=True)
    ap.add_argument("--root", action="append", default=[])
    ap.add_argument("--root-module-prefix", action="append", default=[])
    ap.add_argument("--cwd", default=str(ROOT), help="Lake workspace to run in")
    ap.add_argument("--prefix", default="OAI")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    out = str(Path(a.out).resolve())
    src = TEMPLATE.format(imports="\n".join(f"import {m}" for m in a.imp),
                          roots=", ".join(f"`{r}" for r in a.root),
                          modprefixes=", ".join(f"`{m}" for m in a.root_module_prefix),
                          prefix=a.prefix, out=out)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=os.environ.get("TMPDIR")) as f:
        f.write(src)
        path = f.name
    env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:" + os.environ.get("PATH", ""))
    r = subprocess.run(["lake", "env", "lean", path], cwd=a.cwd, env=env, capture_output=True, text=True)
    os.unlink(path)
    msg = "\n".join(l for l in (r.stdout + r.stderr).splitlines() if not l.startswith("warning:"))
    print(msg)
    return r.returncode


if __name__ == "__main__":
    sys.exit(main())
