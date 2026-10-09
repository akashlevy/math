# Declaration-level tree-shaking

These scripts pruned `OAI/NumberTheory/DirichletL`: every declaration that none of the
quasi-Riemann results uses was deleted in place, and modules left empty were removed. Reachability
is computed inside Lean, from the constants used in the types and proof terms of the roots, so
nothing that a proof depends on is removed. Everything else that a deletion leaves behind is
cleaned up and then checked by rebuilding:

- `variable`, `include`, `omit` and `local notation` commands that nothing can see anymore;
- `open` atoms naming vanished namespaces;
- pruned names in `open NS (..)`.

Run from `lean/`, with the modules below built (`lake build` of the four root modules):

```sh
D=OAI.NumberTheory.DirichletL
# 1. exact reachability (one row per declaration: module, name, range, reachable, ...)
python3 scripts/treeshake/reach.py --import $D.Nonvanishing --import $D.Hecke.Nonvanishing \
  --import $D.QRH --import $D.CubicDyadicDecay \
  --root OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re \
  --root OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re \
  --root OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re \
  --root OAI.riemannZeta_ne_zero_of_twenty_three_twenty_fourths_lt_re \
  --root OAI.DirichletCharacter.LFunction_ne_zero_of_twenty_three_twenty_fourths_lt_re \
  --root-module-prefix $D.QRH --root-module-prefix $D.CubicDyadicDecay \
  --root-module-prefix $D.Nonvanishing --root-module-prefix $D.Hecke.Nonvanishing \
  --root-module-prefix $D.Hecke.ConditionalNonvanishing --prefix OAI --out reach.tsv
# 2. namespaces that exist outside the library (to know which `open`s still resolve)
python3 scripts/treeshake/external_namespaces.py $D.Nonvanishing $D.Hecke.Nonvanishing $D.QRH \
  $D.CubicDyadicDecay --out external-namespaces.txt
# 3. prune in place
python3 scripts/treeshake/treeshake.py --in-place --reach reach.tsv \
  --root-module $D.Nonvanishing --root-module $D.Hecke.Nonvanishing --root-module $D.QRH \
  --root-module $D.CubicDyadicDecay --exempt $D.QRH --exempt $D.CubicDyadicDecay \
  --exempt $D.Nonvanishing --exempt $D.Hecke.Nonvanishing --exempt $D.Hecke.ConditionalNonvanishing \
  --exempt $D.ThetaProduct --exempt $D.EisensteinTheta --exempt $D.Hecke.Theta \
  --exempt $D.Hecke.Family --exempt $D.Hecke.IdealBridge \
  --src-prefix $D --dst-prefix $D --out-dir . --external-namespaces external-namespaces.txt \
  --stats-out treeshake-stats.json
# 4. size of a closure: modules, lines, code lines, import/open lines, non-whitespace characters
python3 scripts/treeshake/measure.py $D.Nonvanishing
```

The roots are the Comparator-checked results of the quasi-Riemann development: 7/8 for ζ,
Dirichlet and Hecke L-functions, and 23/24 for Dirichlet L-functions and ζ. Whole modules are also kept:

- the modules stating those results;
- `CubicDyadicDecay`, which `OAI/NumberTheory/CubicMoment` imports, and which is the only module of
  this directory imported from outside it.

Five modules are exempt from rewriting even though they contain unreachable declarations:
`ThetaProduct`, `EisensteinTheta`, `Hecke.Theta`, `Hecke.Family` and `Hecke.IdealBridge`. The
Comparator challenge `HeckeSevenEighths.lean` restates parts of them verbatim, and Comparator
requires the restated constants to equal the library's exactly, proof terms included. Proof terms
can mention auxiliary lemmas (`foo._proof_1`), which Lean names after the first declaration that
needed them and then shares. Deleting an unreachable declaration earlier in such a file renames
those lemmas, for example `shiftedPair._proof_1` becomes `scaledEvenPair._proof_1`. The proofs stay
valid, but they no longer match the challenge.
