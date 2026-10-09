import OAI.NumberTheory.DirichletL.QRH.ZeroFree
import OAI.NumberTheory.DirichletL.QRH.Extraction
import OAI.NumberTheory.DirichletL.QRH.MeanSquare
import OAI.NumberTheory.DirichletL.QRH.Milestones

/-!
# A quasi-Riemann hypothesis: `ζ(s) ≠ 0` for `Re s > 23/24`

The proof follows the paper
`preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf`, the `ϑ = 1/10` case of
OpenAI's *The Quasi-Riemann Hypothesis* (the 11/12 companion of the 7/8 paper). The modules
`OAI.NumberTheory.DirichletL.QRH.*` state each step of the paper as a Lean theorem; this file
only chains them:

* `OAI.QRH.meanSquare` (Proposition 3.1): the sextic family has square-root cancellation on
  average over rows `u` of norm `≤ D^{11/10}`;
* `OAI.QRH.saving_of_meanSquare` (Proposition 3.2): averaging the rows `u = b⁶` extracts a power
  saving `A^φ(D) ≪ D^{23/24+ε}` for the totient-weighted Möbius sum;
* `OAI.QRH.riemannZeta_ne_zero_of_saving` (Proposition 3.3): a power saving for these sums
  continues `1/ζ_K` holomorphically to `Re s > 23/24`.

The import closure of this module is disjoint from the 7/8 argument chain (probe, detector,
moments): it uses only the shared infrastructure that the 7/8 proof is built on.
-/

namespace OAI

open scoped ContDiff

/-- **Theorem 1.1.** The Riemann zeta function has no zeros in the half-plane `Re s > 23/24`. -/
theorem riemannZeta_ne_zero_of_twenty_three_twenty_fourths_lt_re
    {s : ℂ} (hs : (23 / 24 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  refine QRH.riemannZeta_ne_zero_of_saving (fun W hW hWs ε hε => ?_) hs
  have hsupp : Function.support W ⊆ Set.Icc 1 2 := fun x hx =>
    ⟨le_of_not_gt fun h => hx (hWs x (Or.inl h.le)),
      le_of_not_gt fun h => hx (hWs x (Or.inr h.le))⟩
  exact QRH.saving_of_meanSquare W 1 2 hsupp hW ε hε
    (QRH.meanSquare W 1 2 one_pos hsupp hW (2 * ε) (by positivity))

end OAI
