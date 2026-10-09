import OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands
import OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes
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
open scoped ContDiff
open Set

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem sourceSupportMobius_norm (E : Finset ι) :
    ‖supportMobius (fun i => Ideal.span {p i}) E‖ = 1 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have h := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj E)
  simp only [norm_mul, norm_one] at h
  nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) E)]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeSubsetGenerator_norm_eq_productNorm (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 = primeProductNorm p E := by
  rw [primeSubsetGenerator_norm_sq, primeProductNorm_eq_ideal_norm]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem norm_primeProduct_ge_one (S : Finset ι) :
    1 ≤ ‖eisEmbedding (∏ i ∈ S, p i)‖ := by
  have h := primeProductNorm_ge_one p hp S
  dsimp only [primeProductNorm] at h
  nlinarith [norm_nonneg (eisEmbedding (∏ i ∈ S, p i))]

include hp hinj in
theorem secondSourceCommonCoefficient_norm_le_one
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (G E : Finset ι) :
    ‖secondSourceCommonCoefficient p hg Ψ m c d G E‖ ≤ 1 := by
  have hA := (secondInputCoefficient_norm_le p hg Ψ m c d G).trans (hΨ _)
  have hA2 : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hN := primeProductNorm_ge_one p hp E
  have hμ := sourceSupportMobius_norm p hinj E
  change ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ)‖ = 1 at hμ
  simp only [secondSourceCommonCoefficient, norm_mul, norm_div,
    Complex.norm_of_nonneg (sq_nonneg _), primeSubsetGenerator_norm_eq_productNorm,
    Complex.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp E).le, hμ]
  exact (mul_le_of_le_one_left (div_nonneg zero_le_one (zero_le_one.trans hN))
    hA2).trans ((div_le_one (by linarith)).mpr hN)

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d H S‖ ≤ ‖H S‖ := by
  have he : secondInputCoefficient p hg Ψ m c d H S =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) S * H S := by
    simp only [secondInputCoefficient, mul_one]
  rw [he, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ((secondInputCoefficient_norm_le p hg Ψ m c d S).trans (hΨ _))

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem normalizedColumn_schwartz_bound (g : 𝓢(ℝ, ℂ)) (X : ℝ) (S : Finset ι) :
    ‖normalizedColumn p (fun U => g (columnLog p X U)) S‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
  simp only [normalizedColumn, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact (div_le_self (norm_nonneg _) (norm_primeProduct_ge_one p hp S)).trans (g.norm_le_seminorm ℝ _)

include hp hinj in
theorem residualPairWeight_schwartz_bound
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (g : 𝓢(ℝ, ℂ)) (X : ℝ)
    (G S T : Finset ι) :
    ‖residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S T‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 g) ^ 2 := by
  simp only [residualPairWeight, norm_mul, norm_star, sourceSupportMobius_norm p hinj, one_mul]
  have hS := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S).trans
    (normalizedColumn_schwartz_bound p hp g X (G∪S))
  have hT := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) T).trans
    (normalizedColumn_schwartz_bound p hp g X (G∪T))
  simpa only [pow_two] using mul_le_mul hS hT (norm_nonneg _) (apply_nonneg _ _)

include hp in
theorem residualPairWeight_support_bounds
    (Ψ : O →* ℂ) (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) (G E S T : Finset ι) (hEG : E ⊆ G)
    (hw : residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S T ≠ 0) :
    primeProductNorm p G ≤ X*Real.exp M ∧ primeProductNorm p E ≤ X*Real.exp M ∧
      primeProductNorm p S ≤ X*Real.exp M ∧ primeProductNorm p T ≤ X*Real.exp M := by
  obtain ⟨hS,hT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hG := normalizedColumn_subset_norm_bound p hp g M X hX hgM G S G Finset.subset_union_left hS
  exact ⟨hG, (primeProductNorm_mono p hp hEG).trans hG,
    normalizedColumn_subset_norm_bound p hp g M X hX hgM G S S Finset.subset_union_right hS,
    normalizedColumn_subset_norm_bound p hp g M X hX hgM G T T Finset.subset_union_right hT⟩

end
section

theorem tail_radial_scalar_le (Y E n lengthScale H P : ℝ) (A : ℕ)
    (hY : 0 < Y) (hE : 0 < E) (hn : 1 ≤ n) (hL : 1 ≤ lengthScale)
    (hden : E*n^2 ≤ lengthScale^3) (hH : 0 ≤ H) (hP : 0 ≤ P) :
    (Y/n) * (P / ((min 1 (Y/(E*n^2)))^2 * (1+H)^A)) ≤
      Y*P*(1+lengthScale^3/Y)^2 / (1+H)^A := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he : 0 < E*n^2 := mul_pos hE (sq_pos_of_pos hn0)
  have hs : 0 < Y/(E*n^2) := div_pos hY he
  have hr : 0 ≤ lengthScale^3/Y := div_nonneg (pow_nonneg (zero_le_one.trans hL) _) hY.le
  have hi : (min 1 (Y/(E*n^2)))⁻¹ ≤ 1+lengthScale^3/Y := by
    by_cases h : 1 ≤ Y/(E*n^2)
    · rw [min_eq_left h, inv_one]
      linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), inv_div]
      exact (div_le_div_of_nonneg_right hden hY.le).trans (by linarith)
  have hi0 : 0 ≤ (min 1 (Y/(E*n^2)))⁻¹ := inv_nonneg.mpr (le_min zero_le_one hs.le)
  have hi2 := pow_le_pow_left₀ hi0 hi 2
  have hyn : Y/n ≤ Y := div_le_self hY.le hn
  calc
    _ = (Y/n)*P*((min 1 (Y/(E*n^2)))⁻¹)^2 / (1+H)^A := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hyn hP) hi2 (sq_nonneg _) (mul_nonneg hY.le hP)

theorem sum_pair_indicator {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (U : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, if P a ∧ P b then U else 0) =
      ((s.filter P).card : ℝ)^2 * U := by
  calc
    _ = ∑ a ∈ s.filter P, ∑ b ∈ s.filter P, U := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : P a
      · simp only [h, true_and, ite_true]
      · simp only [h, false_and, ite_false, Finset.sum_const_zero]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, pow_two]; ring

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hp hinj

theorem residualTailCost_polynomial
    (F G E : Finset ι) (hEG : E ⊆ G) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X Y H lengthScale P : ℝ) (A : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hXL : X * Real.exp M ≤ lengthScale) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) :
    residualTailCost p hg F G Ψ Ψ m c d
      (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
      (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P ≤
      if primeProductNorm p G ≤ lengthScale then
        (128*lengthScale)^2 * ((SchwartzMap.seminorm ℝ 0 0 g)^2 *
          (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) else 0 := by
  let C := (SchwartzMap.seminorm ℝ 0 0 g)^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w := residualPairWeight p hg Ψ Ψ m c d
    (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
    (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
  have hsupp (S T : Finset ι) (hw : w S T ≠ 0) :
      primeProductNorm p G ≤ lengthScale ∧ primeProductNorm p E ≤ lengthScale ∧
      primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale := by
    obtain ⟨hG,hE,hS,hT⟩ := residualPairWeight_support_bounds p hp hg Ψ m c d g M X hX hgM G E S T hEG hw
    exact ⟨hG.trans hXL,hE.trans hXL,hS.trans hXL,hT.trans hXL⟩
  by_cases hG : primeProductNorm p G ≤ lengthScale
  · rw [ite_eq_left hG]
    calc
      _ ≤ ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
          if primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale then C else 0 := by
        unfold residualTailCost
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro T hT
        by_cases hd : Disjoint S T
        · rw [ite_eq_left hd]
          dsimp only
          by_cases hw : w S T = 0
          · change ‖w S T‖ * _ ≤ _
            rw [hw, norm_zero, zero_mul]
            split_ifs <;> positivity
          · obtain ⟨_,hE,hSn,hTn⟩ := hsupp S T hw
            rw [ite_eq_left ⟨hSn,hTn⟩]
            have hn2 : ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
                primeProductNorm p S * primeProductNorm p T := active_norm_sq_disjoint p S T hd
            have hn : 1 ≤ ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖ := by
              have hpS := primeProductNorm_ge_one p hp S
              have hpT := primeProductNorm_ge_one p hp T
              have hpST : 1 ≤ primeProductNorm p S * primeProductNorm p T := one_le_mul_of_one_le_of_one_le hpS hpT
              rw [← hn2] at hpST
              nlinarith [norm_nonneg (eisEmbedding (∏ i : activeSupport T S, p i.val))]
            have hNe : 0 < ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 :=
              SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)
            have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
                ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 ≤ lengthScale^3 := by
              rw [primeSubsetGenerator_norm_eq_productNorm, hn2]
              have hST := mul_le_mul hSn hTn (FirstPassCubeLabels.primeProductNorm_pos p hp T).le
                (zero_le_one.trans hL)
              have hEST := mul_le_mul hE hST
                (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
                  (FirstPassCubeLabels.primeProductNorm_pos p hp T).le) (zero_le_one.trans hL)
              nlinarith
            have hscalar := tail_radial_scalar_le Y
              (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2)
              (‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖) lengthScale H P A hY hNe hn hL hden hH hP
            exact mul_le_mul (residualPairWeight_schwartz_bound p hp hg hinj Ψ hΨ m c d g X G S T)
              hscalar (by positivity) (sq_nonneg _)
        · rw [ite_eq_right hd]
          split_ifs <;> positivity
      _ = ((boundedPrimeSupports p (F\G) lengthScale).card : ℝ)^2 * C :=
        sum_pair_indicator (F\G).powerset (fun S => primeProductNorm p S ≤ lengthScale) C
      _ ≤ (128*lengthScale)^2 * C := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (boundedPrimeSupports_card p hinj (F\G) lengthScale hL) 2) hC
  · rw [ite_eq_right hG]
    have hz : residualTailCost p hg F G Ψ Ψ m c d
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P = 0 := by
      unfold residualTailCost
      apply Finset.sum_eq_zero
      intro S hS
      apply Finset.sum_eq_zero
      intro T hT
      by_cases hd : Disjoint S T
      · rw [ite_eq_left hd]
        have hw : w S T = 0 := by
          by_contra hw
          exact hG (hsupp S T hw).1
        change ‖w S T‖ * _ = 0
        rw [hw, norm_zero, zero_mul]
      · rw [ite_eq_right hd]
    exact hz.le

theorem secondSourceTailCost_polynomial
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X Y H lengthScale P : ℝ) (A : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hXL : X * Real.exp M ≤ lengthScale) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
      residualTailCost p hg F G Ψ Ψ m c d
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A P) ≤
      (128*lengthScale)^4 * ((SchwartzMap.seminorm ℝ 0 0 g)^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  let C := (SchwartzMap.seminorm ℝ 0 0 g)^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ 128*lengthScale := by positivity
  calc
    _ ≤ ∑ G ∈ F.powerset, if primeProductNorm p G ≤ lengthScale then (128*lengthScale)^3*C else 0 := by
      apply Finset.sum_le_sum
      intro G hG
      by_cases hGn : primeProductNorm p G ≤ lengthScale
      · rw [ite_eq_left hGn]
        have heq : boundedPrimeSupports p G lengthScale = G.powerset := by
          apply Finset.filter_eq_self.mpr
          intro E hE
          exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hE)).trans hGn
        have hcard : (G.powerset.card : ℝ) ≤ 128*lengthScale := by
          simpa only [heq] using boundedPrimeSupports_card p hinj G lengthScale hL
        calc
          _ ≤ ∑ E : G.powerset, (128*lengthScale)^2*C := by
            apply Finset.sum_le_sum
            intro E hE
            have hr := residualTailCost_polynomial p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
              Ψ hΨ m c d g M X Y H lengthScale P A hX hY hH hP hL hXL hgM
            rw [ite_eq_left hGn] at hr
            have hc := secondSourceCommonCoefficient_norm_le_one p hp hg hinj Ψ hΨ m c d G E.val
            exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans
              (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hC))
          _ = (G.powerset.card : ℝ)*((128*lengthScale)^2*C) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          _ ≤ (128*lengthScale)*((128*lengthScale)^2*C) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hC)
          _ = _ := by ring
      · rw [ite_eq_right hGn]
        apply Finset.sum_nonpos
        intro E hE
        have hr := residualTailCost_polynomial p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
          Ψ hΨ m c d g M X Y H lengthScale P A hX hY hH hP hL hXL hgM
        rw [ite_eq_right hGn] at hr
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr
    _ = ((boundedPrimeSupports p F lengthScale).card : ℝ)*((128*lengthScale)^3*C) := by
      rw [← Finset.sum_filter]
      simp only [boundedPrimeSupports, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128*lengthScale)*((128*lengthScale)^3*C) :=
      mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F lengthScale hL)
        (mul_nonneg (pow_nonneg hB _) hC)
    _ = _ := by ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

end SecondPassArithmetic

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem sqrt_scale_shell_upper (M B b : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hb : B / 2 ≤ b) : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
  simpa only [one_mul, div_one] using principal_middle_prefactor_bound
    M B b 1 1 1 1 hM hB hb (by norm_num) le_rfl (by norm_num) le_rfl

theorem original_middle_rectangle_upper (M B b D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * Real.sqrt (M / b)) :
    D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B) := by
  calc
    _ ≤ d * e := mul_le_mul hd he hD₂ (hD₁.trans hd)
    _ ≤ U * Real.sqrt (M / b) := hcut
    _ ≤ U * (2 * Real.sqrt (M / B)) :=
      mul_le_mul_of_nonneg_left (sqrt_scale_shell_upper M B b hM hB hb) hU
    _ = _ := by ring

theorem dual_middle_rectangle_upper (M F B b N D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : B / 2 ≤ b) (hN : 0 ≤ N) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * (N * Real.sqrt (F / (M * b)))) :
    D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B))) := by
  have harg (z : ℝ) : F / (M * z) = (F / M) / z := by ring
  simp only [harg] at hcut ⊢
  have hh := original_middle_rectangle_upper (F / M) B b D₁ D₂ d e (U * N)
    (div_pos hF hM) hB hb (mul_nonneg hU hN) hD₁ hD₂ hd he
    (by simpa only [mul_assoc] using hcut)
  simpa only [mul_assoc] using hh

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

def dualMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ originalMiddleWindowAt W S T rows left right a b M P h ∧
    originalMiddleWindowAt W S T rows left right a b M P h ≤
      originalMiddleAt W S T rows left right a b M h := by
  classical
  constructor
  · unfold originalMiddleWindowAt
    positivity
  · unfold originalMiddleWindowAt originalMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualMiddleWindowAt W S T rows left right a b M F P h ∧
    dualMiddleWindowAt W S T rows left right a b M F P h ≤
      dualMiddleAt W S T rows left right a b M F h := by
  classical
  constructor
  · unfold dualMiddleWindowAt
    positivity
  · unfold dualMiddleWindowAt dualMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    originalMiddleWindowAt W S T rows left right a b M P h = 0 := by
  classical
  simp only [originalMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    dualMiddleWindowAt W S T rows left right a b M F P h = 0 := by
  classical
  simp only [dualMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

end CanonicalQuadraticSieve

end

end OAI
