import OAI.NumberTheory.DirichletL.QRH.Setup

/-!
# The spine, part 1: from a power saving to a zero-free half-plane (paper Proposition 3.3,
`prop:mellin`)

For `Re s > 1` the Mellin transform `𝓜^φ(s) = ∫₀^∞ A^φ(D) D^{-s} dD/D` (in the library,
`mellin (fun D => weightedCompactSum χ (S q) W D⁻¹) (-s)`, since `weightedCompactSum` at `D⁻¹`
is `A^φ(D)`) equals `Ŵ(s) · ∑ μ(𝔫)ν(𝔫)(φ(𝔫)/N𝔫)N𝔫^{-s}`, with `ν = χ ∘ N`. The Dirichlet series
is `1/(L(s, χ) L(s, χχ₋₃) P_S(s) E_φ(s))`, where `P_S` collects the Euler factors at `S` and
`E_φ` is an Euler product that converges absolutely and is holomorphic for `Re s > 0`
(`corrected_weighted_mellin_identity`; paper (3.7), `eq:weighted-euler`). Here
`L(s, χ) L(s, χχ₋₃) = L_K(s, ν)` is the base change of `L(s, χ)` to `K = ℚ(√-3)`. A saving
`A^φ(D) ≪ D^{23/24+ε}` makes `𝓜^φ` holomorphic on `Re s > 23/24`, so `L(s, χ) L(s, χχ₋₃)`
cannot vanish there: at a zero `ϱ ≠ 1` the identity would force `Ŵ(ϱ) = 0`, which fails for
`W(y) = y^{-ϱ}φ(y)`.
-/

namespace OAI.QRH

open OAI SixthPowerAverage CompactMellinBridge CanonicalRowCompletion ShortDraftHeckeBridge
open Filter Asymptotics
open scoped ContDiff

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

omit [NeZero q] in
/-- A power saving makes the Mellin transform of the weighted sums holomorphic on
`Re s > 23/24`. -/
theorem weightedMellin_analytic (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0) (hsave : ∀ ε > 0, SavingBound χ W 2 ε) :
    AnalyticOnNhd ℂ (fun s : ℂ => mellin (fun D : ℝ => weightedCompactSum χ (S q) W D⁻¹) (-s))
      {s : ℂ | (23 : ℝ) / 24 < s.re} := by
  intro s hsRe
  change (23 : ℝ) / 24 < s.re at hsRe
  set ε := (s.re - 23 / 24) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hf := weightedCompactSum_hasSum χ (S q) W (fun x hx => hs x (Or.inr hx))
  have hlocal := weighted_sum_inv_locallyIntegrableOn_pos (weightedCoeff χ (S q)) W
    (weightedCompactSum χ (S q) W) hW (fun x hx => hs x (Or.inr hx)) hf
  have hzero := weighted_sum_zero_near_small_D (weightedCoeff χ (S q)) (weightedCoeff_zero χ (S q)) W
    (weightedCompactSum χ (S q) W) (fun x hx => hs x (Or.inr hx)) hf
  have hW2 : ∀ x, W x ≠ 0 → x ≤ 2 := fun x hx => by
    by_contra h
    exact hx (hs x (Or.inr (le_of_not_ge h)))
  have hbig : (fun D : ℝ => weightedCompactSum χ (S q) W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ ((23 : ℝ) / 24 + ε)) := by
    obtain ⟨C, _, hbound⟩ := hsave ε hε
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
    have hDpos : 0 < D := by linarith
    have hM : 2 * D ≤ (⌈2 * D⌉₊ : ℝ) := Nat.le_ceil _
    rw [weightedCompactSum_inv_eq χ (S q) W D 2 hDpos hW2 _ hM,
      Real.norm_of_nonneg (Real.rpow_nonneg hDpos.le _)]
    exact hbound _ D hD hM
  exact ShortDraftMellin.inverse_mellin_analytic _ _ hlocal hbig hzero s (by
    change (23 : ℝ) / 24 + ε < s.re
    rw [hεdef]; linarith)

/-- **Proposition 3.3**: if the totient-weighted Möbius sums save a power for every smooth
weight supported in `[1, 2]`, then `L(s, χ) ≠ 0` for `Re s > 23/24`, except at the pole `s = 1`
of the principal character. -/
theorem LFunction_ne_zero_of_saving
    (hsave : ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0) →
      ∀ ε > 0, SavingBound χ W 2 ε)
    {s : ℂ} (hs : (23 : ℝ) / 24 < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hpole) h1
  push Not at h1
  -- the test function `W(y) = y^{-s} φ(y)`, with `Ŵ(s) = ∫ φ(y) dy/y ≠ 0`
  let W : ℝ → ℂ := ConcreteCompactWeight.weight s
  have hW : ContDiff ℝ ∞ W := ConcreteCompactWeight.weight_smooth s
  have hWs : ∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0 := ConcreteCompactWeight.weight_support s
  have hM := weightedMellin_analytic χ W hW hWs (hsave W hW hWs)
  have hE := finiteEulerFactor_analytic χ (S q) (S_prime q) ((23 : ℝ) / 24)
  have hH : AnalyticOnNhd ℂ (SmoothMobiusCorrection.eulerCorrection χ (S q))
      {s : ℂ | (23 : ℝ) / 24 < s.re} :=
    (SmoothMobiusCorrection.eulerCorrection_analytic χ (S q)).mono (by
      intro s hs
      change 0 < s.re
      change (23 : ℝ) / 24 < s.re at hs
      linarith)
  have hWanalytic := compact_weight_mellin_analytic W hW hWs ((23 : ℝ) / 24)
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at h1
  -- `L(s, χ) L(s, χχ₋₃)` has no pole at `s = 1`, since one of the two characters is nontrivial
  have hnotboth : χ ≠ 1 ∨ baseChangeChar χ ≠ 1 := by
    by_cases hc : χ = 1
    · exact Or.inr (baseChangeChar_ne_one_of_one χ hc)
    · exact Or.inl hc
  exact (pair_zero_free_of_identity_gt_two χ (baseChangeChar χ) hnotboth ((23 : ℝ) / 24)
      (by norm_num)
      (fun s => (finiteEulerFactor χ (S q) s * SmoothMobiusCorrection.eulerCorrection χ (S q) s) *
        mellin (fun D : ℝ => weightedCompactSum χ (S q) W D⁻¹) (-s))
      (mellin W) ((hE.mul hH).mul hM) hWanalytic
      (corrected_weighted_mellin_identity χ (S q) (S_prime q) W hW hWs)
      s hs hs1 (ConcreteCompactWeight.weight_mellin_ne_zero s)).1

end OAI.QRH
