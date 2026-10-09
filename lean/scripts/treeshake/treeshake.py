#!/usr/bin/env python3
"""Declaration-level tree-shaking of a Lean library, driven by exact reachability.

Given the table written by reach.py (every declaration of the library, and whether it is reachable
from the root theorems through types and proof terms), deletes every top-level declaration none of
whose constants is reachable, then cleans up what the deletions leave behind:

* kept anyway: closed `rfl`/`simp` lemmas (tactics use them without leaving a trace in proof
  terms), notation, macros and other non-declaration commands;
* deleted too: `example`s; `variable`/`include`/`omit`/`local notation` commands that no surviving
  command can see; `open` atoms naming namespaces that no longer exist (needs
  --external-namespaces); pruned names in `open NS (..)` and `open NS hiding ..`;
* modules left without declarations are deleted, and their importers import their imports.

Usage (from lean/; see README.md for the exact roots used for the quasi-Riemann development):
  python3 scripts/treeshake/treeshake.py --in-place --reach reach.tsv \
      --root-module A --root-module B ... --exempt PREFIX ... \
      --src-prefix OAI.NumberTheory.DirichletL --dst-prefix OAI.NumberTheory.DirichletL \
      --out-dir . --external-namespaces external-namespaces.txt --stats-out treeshake-stats.json
Modules under an --exempt prefix are never rewritten; they and their direct imports are never deleted.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from importgraph import ROOT, closure, local_imports, module_path  # noqa: E402

ATTR_LINE = re.compile(r"^@\[[^\]]*\]\s*$")
IN_PREFIX = re.compile(r"^(omit|include|open|set_option|variable)\b.*\sin\s*$")
GLOBAL_SYNTAX = re.compile(r"^(notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab)\b")
OPEN_SIMPLE = re.compile(r"^open( scoped)? ([\w.' ]+?)\s*$")
SCOPE_OPEN = re.compile(r"^(?:noncomputable )?(namespace|section)\b\s*([\w.']*)")
END = re.compile(r"^end\b\s*([\w.']*)")
IMPORT = re.compile(r"^import\s+(\S+)\s*$")
# Only commands that introduce ordinary declarations may be deleted; notation/syntax/macro
# commands also create constants with source ranges but are never reachable from proofs.
DELETABLE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|nonrec|"
                       r"@\[[^\]]*\])\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b")


def groups_for(decls):
    """Merge nested/overlapping declaration ranges into top-level command groups."""
    out = []
    for name, s, e, used, closed, rfl in sorted(decls, key=lambda d: (d[1], -d[2])):
        if out and s <= out[-1]["e"]:
            g = out[-1]
            g["e"] = max(g["e"], e)
            g["used"] |= used
            g["closed"] &= closed
            g["rfl"] |= rfl
            g["names"].append(name)
        else:
            out.append({"s": s, "e": e, "used": used, "closed": closed, "rfl": rfl, "names": [name]})
    return out


def dedupe_opens(lines):
    """Drop `open` atoms already opened in the current namespace scope chain."""
    stack = [{"ns": "", "opens": set()}]  # frames: namespace path + opened atoms
    out = []
    for line in lines:
        m = SCOPE_OPEN.match(line)
        if m:
            kind, name = m.groups()
            ns = stack[-1]["ns"]
            if kind == "namespace":
                ns = f"{ns}.{name}" if ns else name
            stack.append({"ns": ns, "opens": set()})
            out.append(line)
            continue
        if END.match(line) and len(stack) > 1:
            stack.pop()
            out.append(line)
            continue
        m = OPEN_SIMPLE.match(line)
        if m and not line.rstrip().endswith(" in") and not re.search(r"\s(hiding|renaming)\s", line):
            scoped = bool(m.group(1))
            ns = stack[-1]["ns"]
            seen = set().union(*(f["opens"] for f in stack if f["ns"] == ns))
            atoms = m.group(2).split()
            keep = []
            for a in atoms:
                key_full, key_sc = ("full", a), ("scoped", a)
                if key_full in seen or (scoped and key_sc in seen) or a in keep:
                    continue
                keep.append(a)
                stack[-1]["opens"].add(("scoped" if scoped else "full", a))
            if keep:
                out.append(f"open{' scoped' if scoped else ''} {' '.join(keep)}")
            continue
        out.append(line)
    return out


def collapse_blank(lines):
    out = []
    for line in lines:
        if line.strip() == "" and (not out or out[-1].strip() == ""):
            continue
        out.append(line.rstrip())
    while out and out[-1] == "":
        out.pop()
    return out


NS_CMD = re.compile(r"^\s*namespace\s+([\w.'«»]+)")
SECTION = re.compile(r"^\s*(?:noncomputable\s+)?section\b")
END_CMD = re.compile(r"^\s*end\b")
DECL_NAME = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|nonrec|unsafe)\s+)*"
                       r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+([^\s(:{\[]+)")
NOTATION_SYM = re.compile(r'^local notation(?::\w+)?\s+"([^"]+)"')
OPEN_LINE = re.compile(r"^(\s*)open(\s+scoped)?\s+(.*?)\s*$")


def registered_namespaces(lines: list[str]) -> set[str]:
    """Namespaces a module registers: `namespace` commands, prefixes of dotted declaration names,
    and the names of structures, classes and inductives (their constructors live inside)."""
    out: set[str] = set()
    stack: list[str] = []  # current namespace per open scope

    def cur() -> str:
        return stack[-1] if stack else ""

    def reg(full: str) -> None:
        parts = full.split(".")
        for i in range(1, len(parts) + 1):
            out.add(".".join(parts[:i]))

    for line in lines:
        m = NS_CMD.match(line)
        if m:
            full = f"{cur()}.{m.group(1)}" if cur() else m.group(1)
            reg(full)
            stack.append(full)
            continue
        if SECTION.match(line):
            stack.append(cur())
            continue
        if END_CMD.match(line) and stack:
            stack.pop()
            continue
        m = DECL_NAME.match(line)
        if m and m.group(2) not in ("where", "extends"):
            kind, name = m.groups()
            full = name[len("_root_."):] if name.startswith("_root_.") else (f"{cur()}.{name}" if cur() else name)
            parts = full.split(".")
            if len(parts) > 1:
                reg(".".join(parts[:-1]))
            if kind in ("structure", "class", "inductive"):
                reg(full)
    return out


def drop_dead_opens(final: dict, exempt: set, rename, mods: set, external_file: Path) -> None:
    """Remove `open` atoms that resolve to no namespace visible from the module after pruning.

    A namespace disappears when every declaration under it is pruned and no surviving module
    opens a `namespace` block for it; `open` of a missing namespace is an error. An atom is kept
    if any namespace visible from the module (registered by a module in its import closure, or
    outside the library) equals it or ends with `.atom` -- conservative w.r.t. Lean's resolution
    through the current namespace and earlier `open`s."""
    external = {l.strip() for l in external_file.read_text().splitlines() if l.strip()}
    renamed = {rename(m): m for m in mods}
    reg = {m: registered_namespaces(t) for m, t in final.items()}
    imports = {m: [renamed[i] for i in (IMPORT.match(l).group(1) for l in t if IMPORT.match(l)) if i in renamed and renamed[i] in final]
               for m, t in final.items()}
    closure_memo: dict[str, frozenset] = {}

    def closure_of(m: str) -> frozenset:
        if m not in closure_memo:
            acc = {m}
            for i in imports[m]:
                acc |= closure_of(i)
            closure_memo[m] = frozenset(acc)
        return closure_memo[m]

    sys.setrecursionlimit(100000)
    by_suffix: dict[str, set[str]] = {}
    def index(ns: str, owner: str) -> None:
        parts = ns.split(".")
        for i in range(len(parts)):
            by_suffix.setdefault(".".join(parts[i:]), set()).add(owner)
    for ns in external:
        index(ns, "<external>")
    for m, nss in reg.items():
        for ns in nss:
            index(ns, m)

    def alive(atom: str, m: str) -> bool:
        owners = by_suffix.get(atom, set())
        return "<external>" in owners or bool(owners & closure_of(m))

    dropped = 0
    for m, lines in final.items():
        if m in exempt:
            continue
        out = []
        in_comment = False
        for line in lines:
            if in_comment or line.lstrip().startswith(("/-", "--")):
                out.append(line)
                if line.lstrip().startswith("/-"):
                    in_comment = True
                if "-/" in line:
                    in_comment = False
                continue
            om = OPEN_LINE.match(line)
            if not om or "(" in line or " hiding " in line or " renaming " in line:
                if om and not alive(om.group(3).split()[0], m):
                    dropped += 1  # `open NS (..)`/`hiding` of a vanished namespace: drop the line
                    continue
                out.append(line)
                continue
            indent, scoped, rest = om.groups()
            words = rest.split()
            suffix_in = words[-1] == "in"
            atoms = words[:-1] if suffix_in else words
            keep = [x for x in atoms if alive(x, m)]
            dropped += len(atoms) - len(keep)
            if keep:
                out.append(f"{indent}open{scoped or ''} {' '.join(keep)}{' in' if suffix_in else ''}")
        final[m] = out
    print(f"dropped {dropped} open atoms naming vanished namespaces")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--reach", required=True)
    ap.add_argument("--root-module", action="append", required=True)
    ap.add_argument("--exempt", action="append", default=[],
                    help="module prefix never rewritten or deleted (in-place mode)")
    ap.add_argument("--stats-out", help="where to write the per-module statistics (JSON)")
    ap.add_argument("--external-namespaces",
                    help="file listing every namespace registered outside the pruned library (dumped from "
                         "Lean); enables dropping `open` atoms whose namespace no longer exists")
    ap.add_argument("--src-prefix", required=True)
    ap.add_argument("--dst-prefix", required=True)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--keep", help="file of constant names to force-keep")
    ap.add_argument("--in-place", action="store_true",
                    help="prune the --out-dir library itself (src prefix == dst prefix): rewrite files in "
                         "place and delete emptied modules, instead of regenerating the directory")
    ap.add_argument("--keep-attr", default=r"simps?",
                    help="regex; keep declarations carrying a matching attribute (elaboration-only uses, "
                         "e.g. rfl simp lemmas, never appear in proof terms)")
    a = ap.parse_args()

    decls = defaultdict(list)
    for row in Path(a.reach).read_text().splitlines():
        if not row.strip():
            continue
        mod, name, s, e, u, tc, rf = row.split("\t")
        decls[mod].append((name, int(s), int(e), u == "1", tc == "1", rf == "1"))
    keep_names = set()
    if a.keep and Path(a.keep).is_file():
        keep_names = {l.strip() for l in Path(a.keep).read_text().splitlines() if l.strip() and not l.startswith("#")}
    for mod in decls:
        decls[mod] = [(n, s, e, u or n in keep_names, tc, rf) for n, s, e, u, tc, rf in decls[mod]]

    pruned_names: set[str] = set()  # filled per module below; used to fix `open NS (names)`
    mods, _ = closure(a.root_module)
    mods = {m for m in mods if m == a.src_prefix or m.startswith(a.src_prefix + ".")}
    exempt = {m for m in mods if any(m == e or m.startswith(e + ".") for e in a.exempt)}
    if a.in_place and not a.exempt:  # QRH/: the hand-written root module and its spine
        exempt |= {m for m in mods if m in a.root_module or any(m.startswith(r + ".Spine") for r in a.root_module)}
    rename = lambda m: a.dst_prefix + m[len(a.src_prefix):]  # noqa: E731

    new_text: dict[str, list[str]] = {}
    empty: set[str] = set()
    stats = {}
    for mod in sorted(mods):
        lines = module_path(mod).read_text().split("\n")
        n_orig = len(lines)
        dead = [False] * (n_orig + 2)
        gs = groups_for(decls.get(mod, []))
        attr_re = re.compile(r"@\[[^\]]*\b(" + a.keep_attr + r")\b")
        for g in gs:
            tagged = attr_re.search(lines[g["s"] - 1]) or (g["s"] >= 2 and attr_re.search(lines[g["s"] - 2]))
            if (tagged or g["rfl"]) and g["closed"]:  # lemmas about pruned constants cannot affect kept proofs
                g["used"] = True
        kept_groups = [g for g in gs if g["used"]]
        for g in gs:
            if not g["used"] and not DELETABLE.match(lines[g["s"] - 1]):
                g["used"] = True  # not an ordinary declaration (e.g. notation): keep
            if g["used"]:
                continue
            for i in range(g["s"], g["e"] + 1):
                dead[i] = True
            j = g["s"] - 1  # attribute lines and `... in` prefixes above (blank lines allowed between)
            while j >= 1:
                if lines[j - 1].strip() == "":
                    j -= 1
                    continue
                if ATTR_LINE.match(lines[j - 1]) or IN_PREFIX.match(lines[j - 1]):
                    dead[j] = True
                    j -= 1
                    continue
                if lines[j - 1].rstrip().endswith(" in"):  # multi-line `omit ... in` etc.
                    k = j
                    while k >= 1 and lines[k - 1][:1] in (" ", "\t"):
                        k -= 1
                    if k >= 1 and re.match(r"^(omit|include|open|set_option|variable)\b", lines[k - 1]):
                        for i in range(k, j + 1):
                            dead[i] = True
                        j = k - 1
                        continue
                break
        # `variable`/`include`/`omit`/`local notation` commands that no surviving command can see (none
        # follows them before their scope closes) are dead too; they may mention pruned constants
        # any surviving top-level command may use a variable (not only ranged declarations: e.g. an
        # anonymous `local instance` has no declaration range), so count them all conservatively
        inert = re.compile(r"^(end\b|namespace\b|(noncomputable\s+)?section\b|open\b|variable\b|include\b|"
                           r"omit\b|set_option\b|universe\b|(local\s+|scoped\s+)?notation\b|/-|--|-/|import\b)")
        kept_starts = sorted({g["s"] for g in gs if g["used"]} |
                             {i for i in range(1, n_orig + 1)
                              if not dead[i] and lines[i - 1][:1] not in ("", " ", "\t")
                              and not inert.match(lines[i - 1])})
        close_of: dict[int, int] = {}  # scope-opening line -> closing line
        stack: list[int] = []
        scope_at = [0] * (n_orig + 2)  # innermost open scope at each line (0 = file)
        for i in range(1, n_orig + 1):
            l = lines[i - 1]
            scope_at[i] = stack[-1] if stack else 0
            if NS_CMD.match(l) or SECTION.match(l):
                stack.append(i)
            elif END_CMD.match(l) and stack:
                close_of[stack.pop()] = i
        i = 1
        while i <= n_orig:
            if (lines[i - 1].startswith(("variable", "include", "omit", "local notation"))
                    and not lines[i - 1].rstrip().endswith(" in") and not dead[i]):
                j = i
                while j < n_orig and lines[j][:1] in (" ", "\t") and lines[j].strip():
                    j += 1  # continuation lines of a multi-line `variable`
                end = close_of.get(scope_at[i], n_orig + 1)
                unused_notation = False
                sym = NOTATION_SYM.match(lines[i - 1])
                if sym:  # a local notation that no surviving line in its scope mentions is dead
                    unused_notation = not any(sym.group(1) in lines[t - 1]
                                              for t in range(j + 1, min(end, n_orig + 1)) if not dead[t])
                if unused_notation or not any(i < k < end for k in kept_starts):
                    for t in range(i, j + 1):
                        dead[t] = True
                i = j + 1
                continue
            i += 1
        i = 1
        while i <= n_orig:  # examples run until the next column-0 line
            if lines[i - 1].startswith("example"):
                dead[i] = True
                i += 1
                while i <= n_orig and (lines[i - 1] == "" or lines[i - 1][0] in " \t"):
                    dead[i] = True
                    i += 1
                continue
            i += 1
        for g in gs:
            if not g["used"]:
                pruned_names.update(g["names"])
        body = [lines[i - 1] for i in range(1, n_orig + 1) if not dead[i]]
        has_global_syntax = any(GLOBAL_SYNTAX.match(l) for l in body)
        if not kept_groups and not has_global_syntax and mod not in exempt:
            empty.add(mod)
        new_text[mod] = body
        stats[mod] = {"orig_lines": n_orig, "decl_groups": len(gs), "kept_groups": len(kept_groups)}

    def resolved_imports(mod: str, memo={}) -> list[str]:
        """Local imports of `mod` with removed modules replaced by their own imports."""
        if mod in memo:
            return memo[mod]
        out = []
        for imp in local_imports(mod):
            if imp in mods and imp in empty:
                out += [x for x in resolved_imports(imp) if x not in out]
            elif imp not in out:
                out.append(imp)
        memo[mod] = out
        return out

    explicit_open = re.compile(r"open ([\w.']+) \(([^)]*)\)", re.S)
    hiding_open = re.compile(r"^open ([\w.']+) hiding ([\w.' ]+)$", re.M)

    def fix_explicit_opens(text: str) -> str:
        """Drop pruned names from `open NS (a b c)`; drop the clause if nothing is left."""
        def repl(m):
            ns, names = m.group(1), m.group(2).split()
            keep = [n for n in names
                    if not ({f"OAI.{ns}.{n}", f"{ns}.{n}"} & pruned_names)]
            return f"open {ns} ({' '.join(keep)})" if keep else ""
        text = explicit_open.sub(repl, text)

        def repl_hiding(m):  # `open NS hiding a b`: hiding a pruned name is an error too
            ns, names = m.group(1), m.group(2).split()
            keep = [n for n in names if not ({f"OAI.{ns}.{n}", f"{ns}.{n}"} & pruned_names)]
            return f"open {ns} hiding {' '.join(keep)}" if keep else f"open {ns}"
        return hiding_open.sub(repl_hiding, text)

    out_dir = ROOT / a.out_dir
    if a.in_place:
        if a.src_prefix != a.dst_prefix:
            sys.exit("--in-place requires --src-prefix == --dst-prefix")
        # never delete a root, or a module imported by an exempt (never rewritten) module
        protected = set(a.root_module) | {i for m in exempt for i in local_imports(m)}
        empty -= protected
        for mod in empty:
            module_path(mod).unlink()
    else:
        if (out_dir / "HAND_EDITED").exists():
            sys.exit(f"refusing to overwrite {out_dir}: it is hand-edited source now (see {out_dir}/HAND_EDITED)")
        if out_dir.exists():
            shutil.rmtree(out_dir)
    final: dict[str, list[str]] = {}
    for mod in sorted(mods - empty):
        if mod in exempt:  # hand-written or imported from outside: never rewritten
            final[mod] = module_path(mod).read_text().split("\n")
            continue
        body = [l for l in new_text[mod] if not IMPORT.match(l)]
        imports = []
        for imp in resolved_imports(mod):
            name = rename(imp) if imp in mods else imp
            if name not in imports:
                imports.append(name)
        body = fix_explicit_opens("\n".join(body)).split("\n")
        final[mod] = [f"import {i}" for i in imports] + collapse_blank(dedupe_opens(body))
    if a.external_namespaces:
        drop_dead_opens(final, exempt, rename, mods, ROOT / a.external_namespaces)

    total_new = 0
    for mod in sorted(mods - empty):
        text = final[mod]
        if mod in exempt:
            stats[mod]["new_lines"] = stats[mod]["orig_lines"]
            total_new += stats[mod]["orig_lines"]
            continue
        path = module_path(mod) if a.in_place else out_dir / Path(*rename(mod).split(".")[1:]).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(text).rstrip("\n") + "\n")
        stats[mod]["new_lines"] = len(text)
        total_new += len(text)

    orig_total = sum(s["orig_lines"] for s in stats.values())
    summary = {"modules_before": len(mods), "modules_after": len(mods - empty),
               "lines_before": orig_total, "lines_after": total_new,
               "removed_modules": sorted(empty)}
    stats_out = (ROOT / a.stats_out if a.stats_out else
                 ROOT / "audit" / "treeshake-stats.json" if a.in_place else out_dir / "treeshake-stats.json")
    stats_out.write_text(json.dumps({"summary": summary, "modules": stats}, indent=1))
    print(json.dumps({k: v for k, v in summary.items() if k != "removed_modules"}))
    print(f"removed {len(empty)} modules")
    return 0


if __name__ == "__main__":
    sys.exit(main())
