import OAI.NumberTheory.DirichletL.QRH.ZeroFree
import OAI.NumberTheory.DirichletL.QRH.Extraction
import OAI.NumberTheory.DirichletL.QRH.MeanSquare
import OAI.NumberTheory.DirichletL.QRH.Milestones

/-!
# A quasi-Riemann hypothesis: `L(s, χ) ≠ 0` for `Re s > 23/24`

Every Dirichlet `L`-function, and in particular `ζ`, has no zeros in the half-plane
`Re s > 23/24` (apart from the pole of the principal character at `s = 1`).

The proof follows the paper
`preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf`, the `ϑ = 1/10` case of
OpenAI's *The Quasi-Riemann Hypothesis* (the 11/12 companion of the 7/8 paper), for the Hecke
characters `ν = χ ∘ N` of `K = ℚ(√-3)` that come from Dirichlet characters `χ`. The modules
`OAI.NumberTheory.DirichletL.QRH.*` state each step of the paper as a Lean theorem; this file
only chains them:

* `OAI.QRH.meanSquare` (Proposition 3.1): the sextic family has square-root cancellation on
  average over rows `u` of norm `≤ D^{11/10}`;
* `OAI.QRH.saving_of_meanSquare` (Proposition 3.2): averaging the rows `u = b⁶` extracts a power
  saving `A^φ(D) ≪ D^{23/24+ε}` for the totient-weighted Möbius sum;
* `OAI.QRH.LFunction_ne_zero_of_saving` (Proposition 3.3): a power saving for these sums
  continues `1/(L(s, χ) L(s, χχ₋₃))` holomorphically to `Re s > 23/24`.

The import closure of this module is disjoint from the 7/8 argument chain (probe, detector,
moments): it uses only the shared infrastructure that the 7/8 proof is built on.
-/

namespace OAI

open scoped ContDiff

namespace DirichletCharacter
open scoped _root_.DirichletCharacter

/-- **Theorem 1.1.** Every Dirichlet `L`-function has no zeros in the half-plane `Re s > 23/24`,
apart from the pole of the principal character at `s = 1`. -/
theorem LFunction_ne_zero_of_twenty_three_twenty_fourths_lt_re
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (23 / 24 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  refine QRH.LFunction_ne_zero_of_saving χ (fun W hW hWs ε hε => ?_) (by exact_mod_cast hs) hpole
  have hsupp : Function.support W ⊆ Set.Icc 1 2 := fun x hx =>
    ⟨le_of_not_gt fun h => hx (hWs x (Or.inl h.le)),
      le_of_not_gt fun h => hx (hWs x (Or.inr h.le))⟩
  exact QRH.saving_of_meanSquare χ W 1 2 hsupp hW ε hε
    (QRH.meanSquare χ W 1 2 one_pos hsupp hW (2 * ε) (by positivity))

end DirichletCharacter

/-- **Theorem 1.1** for `ζ` (the principal character of modulus `1`): the Riemann zeta function
has no zeros in the half-plane `Re s > 23/24`. -/
theorem riemannZeta_ne_zero_of_twenty_three_twenty_fourths_lt_re
    {s : ℂ} (hs : (23 / 24 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at h1
  have h := DirichletCharacter.LFunction_ne_zero_of_twenty_three_twenty_fourths_lt_re
    (1 : _root_.DirichletCharacter ℂ 1) hs (fun h => hs1 h.2)
  rwa [_root_.DirichletCharacter.LFunction_modOne_eq] at h

end OAI
