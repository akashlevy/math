import OAI.NumberTheory.DirichletL.QRH.Setup

/-!
# The spine, part 2: extraction from the mean square (paper Proposition 3.2, `prop:extraction`)

The rows `u = b⁶` see the Möbius sum almost untwisted: `χ_𝔫(b⁶) = 1` if `b` is prime to `𝔫`
and `0` otherwise. Averaging `A_{b⁶}` over `N(b) ≤ Y` with a smooth bump `V(N(b)/Y)` therefore
produces `Y · V̂(0) · A^φ(D)` plus a remainder of size `D^{1+ε}` (`totient_sum_normalized_bound`,
`average_remainder_small_power`), while Cauchy–Schwarz against the mean square bounds the
average by `√(Y · D^{21/10+2ε})`. With `Y = D^{11/60}` (so `Y⁶ = D^{11/10}` and the rows lie
in the range of the mean square) this gives `A^φ(D) ≪ D^{137/120+ε} / Y = D^{23/24+ε}`.
-/

namespace OAI.QRH

open OAI ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson SixthPowerAverage
open scoped ContDiff SchwartzMap

/-- **Proposition 3.2** (extraction): the mean square with loss `2ε` gives the power saving
`A^φ(D) ≪ D^{23/24+ε}`. -/
theorem saving_of_meanSquare (W : ℝ → ℂ) (a b : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (ε : ℝ) (hε : 0 < ε)
    (hms : MeanSquareBound W b (2 * ε)) : SavingBound W b ε := by
  classical
  obtain ⟨V, hV, hVs, hV0, hVhat⟩ := exists_averaging_test
  obtain ⟨Cm, hCm, hm⟩ := hms
  obtain ⟨Ce, hCe, he⟩ := average_remainder_small_power ε hε
  have hWc : HasCompactSupport W := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  let Ws : 𝓢(ℝ, ℂ) := hWc.toSchwartzMap hW
  let G : ℝ := SchwartzMap.seminorm ℝ 0 0 Ws
  let B : ℝ := max 1 b
  let Err : ℝ := Ce * G * QuadraticInitialBound.pvControl V * B ^ (1 + ε)
  let Avg : ℝ := Real.sqrt (768 * Cm)
  let C : ℝ := (Avg + Err) / ‖paperRadialFourier V 0‖
  have hG : 0 ≤ G := apply_nonneg _ _
  have hB : 1 ≤ B := le_max_left _ _
  have hErr : 0 ≤ Err := mul_nonneg (mul_nonneg (mul_nonneg hCe.le hG)
    (QuadraticInitialBound.pvControl_nonneg V)) (by positivity)
  have hAvg : 0 < Avg := Real.sqrt_pos.mpr (by positivity)
  have hhat : 0 < ‖paperRadialFourier V 0‖ := norm_pos_iff.mpr hVhat
  refine ⟨C, div_pos (by linarith) hhat, ?_⟩
  intro M D hD hM
  have hDpos : 0 < D := by linarith
  -- the rows: `u = b⁶` with `N(b) ≤ Y = D^{11/60}`, so `N(u) ≤ Y⁶ = D^{11/10}`
  let Y : ℝ := D ^ ((11 : ℝ) / 60)
  have hY : 1 ≤ Y := Real.one_le_rpow hD (by norm_num)
  have hYp : 0 < Y := by linarith
  let F := ideals M
  let Arow : O → ℂ := A W D M
  have hYpow : Y ^ 6 = D ^ ((11 : ℝ) / 10) := by
    dsimp only [Y]
    rw [← Real.rpow_mul_natCast hDpos.le]
    norm_num
  -- the mean square over these rows
  have hms : (∑ z ∈ (averagingRows Y).image (fun b => b ^ 6), ‖Arow z‖ ^ 2) ≤
      Cm * D ^ ((21 : ℝ) / 10 + 2 * ε) :=
    hm M D hD hM _ fun z hz => by
      have hn := averagingRows_power_norm Y hY hz
      exact ⟨hn.1, hYpow ▸ hn.2⟩
  -- Cauchy–Schwarz over the at most `768 Y` rows
  have havg2 := (average_tsum_cauchy V hV hVs hV0 Y hY Arow).trans
    (mul_le_mul_of_nonneg_left hms (by positivity : 0 ≤ 768 * Y))
  have heq : 768 * Y * (Cm * D ^ ((21 : ℝ) / 10 + 2 * ε)) =
      (Avg * D ^ ((137 : ℝ) / 120 + ε)) ^ 2 := by
    dsimp only [Y, Avg]
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 768 * Cm), ← Real.rpow_mul_natCast hDpos.le]
    calc
      _ = (768 * Cm) * (D ^ ((11 : ℝ) / 60) * D ^ ((21 : ℝ) / 10 + 2 * ε)) := by ring
      _ = (768 * Cm) * D ^ ((11 : ℝ) / 60 + ((21 : ℝ) / 10 + 2 * ε)) := by
        rw [← Real.rpow_add hDpos]
      _ = _ := by congr 2; ring
  rw [heq] at havg2
  have havg : ‖∑' z : O, V (‖eisEmbedding z‖ ^ 2 / Y) * Arow (z ^ 6)‖ ≤
      Avg * D ^ ((137 : ℝ) / 120 + ε) := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp havg2
  -- the remainder from counting `b` prime to `𝔫` is `≪ D^{1+ε}`
  have herr : ‖∑ I ∈ F,
      ShortDraftHeckeBridge.baseChangeWeight χ₁ I * W ((Ideal.absNorm I : ℝ) / D) *
      maskedPrincipalRemainder (fun i : ConcretePrimeRowBridge.primePool F => i.val)
        (ConcretePrimeRowBridge.idealSupport F I) V Y‖ ≤ Err * D ^ (1 + ε) := by
    have hbD : 1 ≤ B * D := by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hD)]
    have hh := he F (ConcretePrimeRowBridge.outsideIdealsUpTo_ne_bot S M) χ₁ (fun n => W (n / D))
      V Y (B * D) G hYp hbD hG (fun n => Ws.norm_le_seminorm ℝ (n / D)) (by
        intro I _ hn
        have hh := (hs hn).2
        exact ((div_le_iff₀ hDpos).mp hh).trans
          (mul_le_mul_of_nonneg_right (le_max_right 1 b) hDpos.le))
    calc
      _ ≤ Ce * G * QuadraticInitialBound.pvControl V * (B * D) ^ (1 + ε) := hh
      _ = Err * D ^ (1 + ε) := by
        rw [Real.mul_rpow (by linarith : 0 ≤ B) hDpos.le]; dsimp only [Err]; ring
  have hexponent : D ^ (1 + ε) ≤ D ^ ((137 : ℝ) / 120 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  -- the average equals `Y · V̂(0) · A^φ(D)` plus that remainder
  have hmain := totient_sum_normalized_bound F (ConcretePrimeRowBridge.outsideIdealsUpTo_ne_bot S M)
    (InitialMeanSquare.outside_good S M bad_subset_S) χ₁ (fun n => W (n / D)) V Y hYp
  have hbound : Y * ‖paperRadialFourier V 0‖ * ‖weightedSum W D M‖ ≤
      (Avg + Err) * D ^ ((137 : ℝ) / 120 + ε) := by
    apply hmain.trans
    have := add_le_add havg (herr.trans (mul_le_mul_of_nonneg_left hexponent hErr))
    simpa only [Arow, A, F, ideals, add_mul] using this
  have hzexp : D ^ ((137 : ℝ) / 120 + ε) = Y * D ^ ((23 : ℝ) / 24 + ε) := by
    dsimp only [Y]
    rw [← Real.rpow_add hDpos]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (mul_pos hYp hhat)).mp
  apply hbound.trans_eq
  rw [hzexp]
  dsimp only [C]
  field_simp [hhat.ne']

end OAI.QRH
