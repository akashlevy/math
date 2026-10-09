import OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open ActualEisensteinCubic
open RationalPrimeExtraction ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteEulerRestoration

theorem tsum_dvd_shift {N : ℕ} (hN : 0 < N)
    (b : ℕ → ℂ) (φ : ℕ → ℂ) :
    (∑' n : ℕ, if N ∣ n then b (n / N) * φ n else 0) =
      ∑' m : ℕ, b m * φ (N * m) := by
  classical
  let f : ℕ → ℂ := fun n => if N ∣ n then b (n / N) * φ n else 0
  let g : ℕ → ℂ := fun m => b m * φ (N * m)
  have hindex (m : ℕ) : f (N * m) = g m := by
    simp [f, g, hN]
  change (∑' n : ℕ, f n) = ∑' m : ℕ, g m
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x : Function.support g => N * x.1) ?_ ?_ ?_
  · intro x y hxy
    apply Subtype.ext
    exact Nat.mul_left_cancel hN hxy
  · intro n hn
    have hdiv : N ∣ n := by
      by_contra hnot
      have : f n = 0 := by simp [f, hnot]
      exact hn this
    let m := n / N
    have hnm : N * m = n := Nat.mul_div_cancel' hdiv
    have hgm : g m ≠ 0 := by
      intro hg
      apply hn
      rw [← hnm, hindex, hg]
    exact ⟨⟨m, hgm⟩, hnm⟩
  · intro x
    exact hindex x.1

theorem tsum_restore_one_prime {N : ℕ} (hN : 0 < N)
    (c : ℂ) (a b φ : ℕ → ℂ)
    (hcoeff : ∀ n, a n = b n + if N ∣ n then c * b (n / N) else 0)
    (hb : Summable (fun n => b n * φ n))
    (hshift : Summable (fun m => b m * φ (N * m))) :
    (∑' n : ℕ, a n * φ n) =
      (∑' n : ℕ, b n * φ n) +
        c * (∑' m : ℕ, b m * φ (N * m)) := by
  classical
  let f : ℕ → ℂ := fun n => if N ∣ n then b (n / N) * φ n else 0
  have hcomp : (fun m => f (N * m)) = (fun m => b m * φ (N * m)) := by
    funext m
    simp [f, hN]
  have hinj : Function.Injective (fun m : ℕ => N * m) :=
    fun _ _ h => Nat.mul_left_cancel hN h
  have hsupport : ∀ n, n ∉ Set.range (fun m : ℕ => N * m) → f n = 0 := by
    intro n hn
    have hnot : ¬N ∣ n := by
      intro hd
      exact hn ⟨n / N, Nat.mul_div_cancel' hd⟩
    simp [f, hnot]
  have hf : Summable f := by
    rw [← (hinj.summable_iff hsupport)]
    change Summable (fun m => f (N * m))
    rw [hcomp]
    exact hshift
  have hfc : Summable (fun n => c * f n) := hf.mul_left c
  have hpoint (n : ℕ) : a n * φ n = b n * φ n + c * f n := by
    rw [hcoeff n]
    by_cases hd : N ∣ n
    · simp [f, hd]
      ring
    · simp [f, hd]
  calc
    (∑' n : ℕ, a n * φ n) = ∑' n : ℕ, (b n * φ n + c * f n) := by
      congr 1
      funext n
      exact hpoint n
    _ = (∑' n : ℕ, b n * φ n) + ∑' n : ℕ, c * f n :=
      hb.tsum_add hfc
    _ = (∑' n : ℕ, b n * φ n) + c * (∑' m : ℕ, b m * φ (N * m)) := by
      rw [tsum_mul_left, tsum_dvd_shift hN b φ]

end FiniteEulerRestoration

namespace FiniteSFactor

end FiniteSFactor

namespace CompactMellinBridge

theorem mellin_weighted_sum
    (a : ℕ → ℂ) (W F : ℝ → ℂ) (s : ℂ)
    (ha0 : a 0 = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖))
    (hlsum : LSeriesSummable a s) :
    mellin (fun D : ℝ => F D⁻¹) (-s) =
      mellin W s * LSeries a s := by
  have hterm (n : ℕ) :
      (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        mellin W s * LSeries.term a s n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0, LSeries.term_zero]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hscale := mellin_comp_mul_left W s hnpos
      have hmul : mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s =
          a n * mellin (fun t : ℝ => W ((n : ℝ) * t)) s := by
        simpa only [smul_eq_mul] using
          (mellin_const_smul (fun t : ℝ => W ((n : ℝ) * t)) s (a n))
      change mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s = _
      rw [hmul, hscale, LSeries.term_of_ne_zero hn]
      simp only [smul_eq_mul, Complex.ofReal_natCast, Complex.cpow_neg]
      ring
  have hsum :
      (∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) :=
    integral_tsum_of_summable_integral_norm hint hsumint
  have hseries :
      (∑' n : ℕ, mellin W s * LSeries.term a s n) =
        mellin W s * LSeries a s := by
    simpa only [LSeries] using hlsum.hasSum.mul_left (mellin W s) |>.tsum_eq
  calc
    mellin (fun D : ℝ => F D⁻¹) (-s) = mellin F s := by
      simpa using mellin_comp_inv F (-s)
    _ = ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (t : ℂ) ^ (s - 1) * F t =
        ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))
      rw [← (hF t ht).tsum_eq]
      rw [← tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := hsum.symm
    _ = ∑' n : ℕ, mellin W s * LSeries.term a s n := by simp_rw [hterm]
    _ = mellin W s * LSeries a s := hseries

theorem weighted_sum_zero_of_large_t
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W F : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (t : ℝ) (ht : 2 ≤ t) : F t = 0 := by
  have hterm (n : ℕ) : a n * W ((n : ℝ) * t) = 0 := by
    by_cases hn : n = 0
    · simp [hn, ha0]
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnt : 2 ≤ (n : ℝ) * t := by
        calc
          2 ≤ t := ht
          _ = (1 : ℝ) * t := by ring
          _ ≤ (n : ℝ) * t :=
            mul_le_mul_of_nonneg_right hn1 (by linarith)
      simp [hW _ hnt]
  have hzero : HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) 0 := by
    simpa only [hterm] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  exact (hF t (lt_of_lt_of_le (by norm_num) ht)).unique hzero

theorem weighted_sum_zero_near_small_D
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W F : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with D hD
  have hDpos : 0 < D := hD.1
  have hDsmall : D < 1 / 2 := hD.2
  have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDsmall) hDinvpos.le
  have hinv : 2 ≤ D⁻¹ := by
    rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
    nlinarith
  exact weighted_sum_zero_of_large_t a ha0 W F hW hF D⁻¹ hinv

theorem compact_weight_mellin_analytic
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (σ : ℝ) :
    AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re} := by
  let A : ℝ → ℂ := fun D => W D⁻¹
  have hcont : ContinuousOn A (Set.Ioi (0 : ℝ)) := by
    have hcontW : ContinuousOn W Set.univ := hW.continuous.continuousOn
    apply hcontW.comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    simp
  have hlocal : LocallyIntegrableOn A (Set.Ioi (0 : ℝ)) :=
    hcont.locallyIntegrableOn measurableSet_Ioi
  have hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with D hD
    have hDpos : 0 < D := hD.1
    have hDsmall : D < 1 / 2 := hD.2
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDsmall) hDinvpos.le
    have hinv : 2 ≤ D⁻¹ := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inr hinv)
  have hzeroTop : A =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right hD hDinvpos.le
    have hinv : D⁻¹ ≤ 1 := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inl hinv)
  have htop : A =O[atTop] (fun D : ℝ => D ^ σ) :=
    hzeroTop.isBigO.trans (isBigO_zero _ _)
  have hM := ShortDraftMellin.inverse_mellin_analytic A σ hlocal htop hzero
  simpa only [A, mellin_comp_inv, neg_neg] using hM

end CompactMellinBridge

end

end OAI
