import OAI.NumberTheory.DirichletL.QuadraticSieve.DivisorBlocks
import OAI.NumberTheory.DirichletL.CubicSieve.IntegratedTransfer
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

namespace JointLogSeparation

theorem finite_triple_bounded_integral {α : Type*} (s : Finset α)
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (F : α → Frequency → ℂ)
    (hF : ∀ i ∈ s, Continuous (F i)) (M : α → ℝ)
    (hM : ∀ i ∈ s, ∀ q, ‖F i q‖ ≤ M i) :
    (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * F i (t₁,t₂,t₃)) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * (∑ i ∈ s, F i (t₁,t₂,t₃)) := by
  have hc : Continuous (fun q => ∑ i ∈ s, F i q) := continuous_finsetSum _ hF
  have hb (q : Frequency) : ‖∑ i ∈ s, F i q‖ ≤ ∑ i ∈ s, M i :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hM i hi q))
  have hi (i : α) (hi : i ∈ s) := tripleCoefficient_bounded_integrable b₁ b₂ b₃ (F i) (hF i hi) (M i) (hM i hi)
  have hs := tripleCoefficient_bounded_integrable b₁ b₂ b₃ (fun q => ∑ i ∈ s, F i q) hc _ hb
  calc
    _ = ∑ i ∈ s, ∫ q : Frequency, tripleCoefficient b₁ b₂ b₃ q * F i q := by
      apply Finset.sum_congr rfl
      intro i hmem
      exact nested_eq_integral _ (hi i hmem)
        (tripleCoefficient_slice_integrable b₁ b₂ b₃ (F i) (hF i hmem) (M i) (hM i hmem))
    _ = ∫ q : Frequency, ∑ i ∈ s, tripleCoefficient b₁ b₂ b₃ q * F i q :=
      (integral_finsetSum s hi).symm
    _ = ∫ q : Frequency, tripleCoefficient b₁ b₂ b₃ q * (∑ i ∈ s, F i q) := by
      simp only [Finset.mul_sum]
    _ = _ := (nested_eq_integral _ hs
      (tripleCoefficient_slice_integrable b₁ b₂ b₃ (fun q => ∑ i ∈ s, F i q) hc _ hb)).symm

end JointLogSeparation

namespace SecondPassIntegration

section
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)
open FourierBridge (logPhase)

def tupleOuterWeight (V : Fin 7 → ℝ → ℂ) (w : OldTuple → ℂ)
    (z ud ue uv kap : OldTuple → ℝ) (q : Frequency) (x : OldTuple) : ℂ :=
  w x * outerWindow V (z x) (ud x) (ue x) (uv x) (kap x) *
    logPhase (q.1 + q.2.1) (z x) * logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)

lemma tupleOuterWeight_continuous (V : Fin 7 → ℝ → ℂ) (w : OldTuple → ℂ)
    (z ud ue uv kap : OldTuple → ℝ) (x : OldTuple) :
    Continuous (fun q => tupleOuterWeight V w z ud ue uv kap q x) := by
  have h₁ : Continuous (fun q : Frequency => logPhase (q.1 + q.2.1) (z x)) :=
    (FourierBridge.logPhase_continuous_left (z x)).comp
    (continuous_fst.add continuous_snd.fst)
  have h₂ : Continuous (fun q : Frequency => logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)) :=
    (FourierBridge.logPhase_continuous_left (kap x - ud x - 2 * ue x - 2 * uv x)).comp
    continuous_snd.snd
  unfold tupleOuterWeight
  fun_prop

lemma tupleOuterWeight_norm (V : Fin 7 → ℝ → ℂ) (w : OldTuple → ℂ)
    (z ud ue uv kap : OldTuple → ℝ) (q : Frequency) (x : OldTuple) :
    ‖tupleOuterWeight V w z ud ue uv kap q x‖ =
      ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ := by
  simp only [tupleOuterWeight, norm_mul, FourierBridge.logPhase_norm, mul_one]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def tupleSourceSum (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (label x)
    (newRow x) (-newRow x) A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem tupleSource_eq_integratedSecondMode
    (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W b : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ R : ℝ)
    (hsep : ∀ x ∈ s,
      postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R =
      separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
        A₁ A₂ b V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂) :
    tupleSourceSum p hp hcop hg s w label F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
      integratedSecondMode p hp hcop hg (𝓕 A₁) (𝓕 A₂) b s
        (tupleOuterWeight V w z ud ue uv kap) label F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ := by
  let Q : OldTuple → Frequency → ℂ := fun x q =>
    tupleOuterWeight V w z ud ue uv kap q x *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ q.1 q.2.2 true) (label x) (newRow x)) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ q.2.1 q.2.2 false) (label x) (-newRow x)
  let M : OldTuple → ℝ := fun x =>
    (‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖) *
      rowMagnitude p hp hcop hg F Ψ₁ m (label x) (newRow x) (V 5) X₁ true *
      rowMagnitude p hp hcop hg F Ψ₂ m (label x) (-newRow x) (V 6) X₂ false
  have hc (x : OldTuple) : Continuous (Q x) := by
    have hw := tupleOuterWeight_continuous V w z ud ue uv kap x
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (label x) (newRow x) (V 5) X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (label x) (-newRow x) (V 6) X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hw.mul h₁.star).mul h₂
  have hbound (x : OldTuple) (q : Frequency) : ‖Q x q‖ ≤ M x := by
    dsimp only [Q, M]
    rw [norm_mul, norm_mul, norm_star, tupleOuterWeight_norm]
    have h₁ := fixedRow_norm_le p hp hcop hg F Ψ₁ m (label x) (newRow x) (V 5) X₁ q.1 q.2.2 true
    have h₂ := fixedRow_norm_le p hp hcop hg F Ψ₂ m (label x) (-newRow x) (V 6) X₂ q.2.1 q.2.2 false
    have hn₁ := rowMagnitude_nonneg p hp hcop hg F Ψ₁ m (label x) (newRow x) (V 5) X₁ true
    have hn₂ := rowMagnitude_nonneg p hp hcop hg F Ψ₂ m (label x) (-newRow x) (V 6) X₂ false
    gcongr
  calc
    _ = ∑ x ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * Q x (t₁,t₂,t₃) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsep x hx]
      unfold separatedPostCommon
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      dsimp [tripleCoefficient, Q, tupleOuterWeight]
      ring
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * (∑ x ∈ s, Q x (t₁,t₂,t₃)) :=
      finite_triple_bounded_integral s (𝓕 A₁) (𝓕 A₂) b Q (fun x _ => hc x) M (fun x _ => hbound x)
    _ = _ := rfl

end

open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

end SecondPassIntegration

section

namespace JointLogSeparation

def halfNormalizationMultiplier (U : ℝ → ℂ) (s : ℝ) : ℂ :=
  U s * (Real.exp (-s / 2) : ℂ)

lemma halfNormalization_temperate (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) : (halfNormalizationMultiplier U).HasTemperateGrowth := by
  apply (hUc.mul_right : HasCompactSupport (halfNormalizationMultiplier U)).hasTemperateGrowth
  change ContDiff ℝ ∞ (fun s : ℝ => U s * (Real.exp (-s / 2) : ℂ))
  have he : ContDiff ℝ ∞ (fun s : ℝ => Real.exp (-s / 2)) := by fun_prop
  exact hUs.mul (Complex.ofRealCLM.contDiff.comp he)

def halfNormalizationCLM (U : ℝ → ℂ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (halfNormalizationMultiplier U)).restrictScalars ℝ

lemma halfNormalizationCLM_apply (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    halfNormalizationCLM U g s = U s * (Real.exp (-s / 2) : ℂ) * g s := by
  exact SchwartzMap.smulLeftCLM_apply_apply (halfNormalization_temperate U hUc hUs) g s

lemma sqrt_exp_half (s : ℝ) : Real.sqrt (Real.exp s) = Real.exp (s / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos s).le (Real.exp_pos (s / 2)).le).mpr
  rw [← Real.exp_add]
  congr 1
  ring

theorem halfNormalization_exact (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1) (s : ℝ) :
    halfNormalizationCLM U g s = g s / (Real.sqrt (Real.exp s) : ℂ) := by
  rw [halfNormalizationCLM_apply U hUc hUs]
  by_cases hg : g s = 0
  · simp [hg]
  rw [hU s hg, one_mul, sqrt_exp_half]
  have he : (Real.exp (-s / 2) : ℂ) = ((Real.exp (s / 2) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Real.exp_neg]
    congr 2
    ring
  rw [he]
  exact (div_eq_inv_mul (g s) (Real.exp (s / 2) : ℂ)).symm

lemma halfNormalization_twist (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    halfNormalizationCLM U (frequencyTwist g t) = frequencyTwist (halfNormalizationCLM U g) t := by
  ext s
  simp only [halfNormalizationCLM_apply U hUc hUs, frequencyTwist_apply]
  ring

end JointLogSeparation

namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels

lemma sqrtProductNorm {ι : Type*} (p : ι → O) (S : Finset ι) :
    Real.sqrt (primeProductNorm p S) = ‖ConcreteTraceCRT.eisEmbedding (∏ i ∈ S, p i)‖ := by
  simp only [primeProductNorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem columnLog_union_scale {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀) :
    columnLog p X (V ∪ N) =
      Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N := by
  have hV := primeProductNorm_pos p hp V
  have hN := primeProductNorm_pos p hp N
  unfold columnLog
  rw [primeProductNorm_union p V N hVN, ← Real.log_mul
    (ne_of_gt (div_pos (mul_pos hV hX₀) hX)) (ne_of_gt (div_pos hN hX₀))]
  congr 1
  field_simp

lemma halfNormalization_at_ratio (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1)
    (N X : ℝ) (hN : 0 < N) (hX : 0 < X) :
    halfNormalizationCLM U g (Real.log (N / X)) / (Real.sqrt X : ℂ) =
      g (Real.log (N / X)) / (Real.sqrt N : ℂ) := by
  rw [halfNormalization_exact U hUc hUs g hU, Real.exp_log (div_pos hN hX), div_div]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_pos hN hX).le]
  congr 2
  field_simp

theorem normalizedColumn_union_test {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1) :
    normalizedColumn p (fun S => g (columnLog p X S)) (V ∪ N) =
      halfNormalizationCLM U g
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) / (Real.sqrt X : ℂ) := by
  rw [← columnLog_union_scale p hp V N hVN X X₀ hX hX₀]
  change g (Real.log (primeProductNorm p (V ∪ N) / X)) /
    (‖ConcreteTraceCRT.eisEmbedding (∏ i ∈ V ∪ N, p i)‖ : ℂ) = _
  rw [← sqrtProductNorm]
  exact (halfNormalization_at_ratio U hUc hUs g hU (primeProductNorm p (V ∪ N)) X
    (primeProductNorm_pos p hp _) hX).symm

end SecondPassIntegration
end

namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

lemma lambdaIdeal_maximal : (Ideal.span {lambda} : Ideal O).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible PrimaryIdealUnitReindex.lambda_prime_actual.irreducible

lemma twoIdeal_maximal : (Ideal.span {(2 : O)} : Ideal O).IsMaximal := by
  simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal

lemma twoIdeal_characteristic : ringChar (O ⧸ Ideal.span {(2 : O)}) = 2 := by
  rw [← Ideal.span_singleton_neg (2 : O)]
  exact cubicTwoIdeal_residue_char

theorem supported_span_iff (z : O) :
    Supported (Ideal.span {z}) ↔ ¬lambda ∣ z ∧ ¬(2 : O) ∣ z := by
  constructor
  · intro h
    constructor
    · intro hz
      have hm : (Ideal.span {lambda} : Ideal O) ∈
          UniqueFactorizationMonoid.normalizedFactors (Ideal.span {z}) := by
        apply (Ideal.mem_normalizedFactors_iff h.1).mpr
        exact ⟨lambdaIdeal_maximal.isPrime,
          (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hz)⟩
      exact (h.2 _ hm).1 (Ideal.subset_span (by simp))
    · intro hz
      have hm : (Ideal.span {(2 : O)} : Ideal O) ∈
          UniqueFactorizationMonoid.normalizedFactors (Ideal.span {z}) := by
        apply (Ideal.mem_normalizedFactors_iff h.1).mpr
        exact ⟨twoIdeal_maximal.isPrime,
          (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hz)⟩
      exact (h.2 _ hm).2 twoIdeal_characteristic
  · rintro ⟨hLam, htwo⟩
    have hz : z ≠ 0 := fun heq => hLam (heq ▸ dvd_zero lambda)
    refine ⟨Ideal.span_singleton_eq_bot.not.mpr hz, ?_⟩
    intro P hP
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hzP : z ∈ P := ((Ideal.mem_normalizedFactors_iff
      (Ideal.span_singleton_eq_bot.not.mpr hz)).mp hP).2 (Ideal.subset_span (by simp))
    constructor
    · intro hlambdaP
      have heq := maximal_ideal_eq_span_of_mem P inferInstance lambda lambdaIdeal_maximal hlambdaP
      rw [heq] at hzP
      exact hLam (Ideal.mem_span_singleton.mp hzP)
    · intro hchar
      have htwoP : (2 : O) ∈ P := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hzero : (2 : O ⧸ P) = 0 := (ringChar.spec (O ⧸ P) 2).mpr (by rw [hchar])
        simpa only [map_ofNat] using hzero
      have heq := maximal_ideal_eq_span_of_mem P inferInstance (2 : O) twoIdeal_maximal htwoP
      rw [heq] at hzP
      exact htwo (Ideal.mem_span_singleton.mp hzP)

def badPrime (i : Bool) : Ideal O := if i then Ideal.span {(2 : O)} else Ideal.span {lambda}

theorem badPrime_mask (z : O) :
    rowCoprimeMask badPrime Finset.univ z = if Supported (Ideal.span {z}) then 1 else 0 := by
  rw [supported_span_iff]
  simp only [rowCoprimeMask, Finset.mem_univ, true_and, Bool.exists_bool, badPrime,
    Bool.false_eq_true, ite_false, ite_true, Ideal.mem_span_singleton]
  by_cases hLam : lambda ∣ z <;> by_cases htwo : (2 : O) ∣ z <;> simp [hLam, htwo]

open CompletedGauss FiniteSieveOperator

theorem highKernelNorm_mono {M N K M' N' K' : ℝ}
    (hM : M ≤ M') (hN : N ≤ N') (hK : K' ≤ K) :
    highKernelNorm M N K ≤ highKernelNorm M' N' K' := by
  let r : highKernelRange M K → highKernelRange M' K' := fun I => ⟨I.val, by
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp I.property
    exact mem_highKernelRange.mpr ⟨hs, hn.trans hM, hK.trans_lt hk⟩⟩
  have hr : Function.Injective r := fun I J h =>
    Subtype.ext (congrArg (fun I : highKernelRange M' K' => I.val) h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hr
    (rangeInclusion hN) (rangeInclusion_injective hN) (highKernelMatrix M' N' K')
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem highKernel_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖operator (fun i j => quadraticRow (cols j) (primaryGenerator (rows i)))‖ ^ 2 ≤
      highKernelNorm M N K := by
  let r : m → highKernelRange M K := fun i => ⟨rows i, hrows i⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (highKernelMatrix M N K)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2
theorem highKernel_quotient_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hdiv : ∀ j, D ∣ cols j) (M N K : ℝ)
    (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)))‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
  apply highKernel_family_squared_norm_le rows (fun j => idealQuotient D (cols j)) hr
  · intro j k heq
    exact hc (idealQuotient_injective_on D (hdiv j) (hdiv k) heq)
  · exact hrows
  · intro j
    exact ⟨admissible_idealQuotient (hcols j).1 (hdiv j),
      idealQuotient_norm_le hD (hdiv j) N (hcols j).2⟩

theorem highKernel_quotientMatrix_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols) (M N K : ℝ)
    (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (quotientMatrix D rows cols)‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
  let S : Finset n := Finset.univ.filter (fun j => D ∣ cols j)
  let A : Matrix m S ℂ := fun i j =>
    quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i))
  have hnorm : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
    apply highKernel_quotient_family_squared_norm_le D hD rows (fun j : S => cols j.val) hr
      (hc.comp Subtype.val_injective)
    · intro j
      exact (Finset.mem_filter.mp j.property).2
    · exact hrows
    · intro j
      exact hcols j.val
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (highKernelNorm_nonneg _ _ _)
  intro a
  have hinner (i : m) : (∑ j, quotientMatrix D rows cols i j * a j) =
      ∑ j : S, A i j * a j.val := by
    change (∑ j, (if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0) * a j) =
      ∑ j : S, quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i)) * a j.val
    rw [Finset.sum_coe_sort S (fun j : n =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) * a j)]
    simp only [S, Finset.sum_filter, ite_mul, zero_mul]
  simp_rw [hinner]
  have henergy := FiniteSieveOperator.energy_bound A (fun j : S => a j.val)
  apply henergy.trans
  calc
    _ ≤ highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K * ∑ j : S, ‖a j.val‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (highKernelNorm_nonneg _ _ _)
      rw [Finset.sum_coe_sort S (fun j : n => ‖a j‖ ^ 2)]
      exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)

open IdealCoprimeSieveOperator

def totalQuotient (D I : Ideal O) : Ideal O := if D ∣ I then idealQuotient D I else 1

theorem totalQuotient_ne_zero (D I : Ideal O) (hI : Admissible I) : totalQuotient D I ≠ 0 := by
  by_cases h : D ∣ I
  · simpa only [totalQuotient, ite_eq_left h] using (admissible_idealQuotient hI h).1
  · simp [totalQuotient, h]

theorem totalQuotient_norm_le (D I : Ideal O) (hI : Admissible I)
    (N : ℝ) (hN : 1 ≤ N) (hIN : (Ideal.absNorm I : ℝ) ≤ N) :
    (Ideal.absNorm (totalQuotient D I) : ℝ) ≤ N := by
  by_cases h : D ∣ I
  · rw [totalQuotient, ite_eq_left h]
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    exact (Nat.cast_le.mpr (Nat.le_of_dvd hn (map_dvd Ideal.absNorm (idealQuotient_dvd h)))).trans hIN
  · simpa only [totalQuotient, ite_eq_right h, map_one, Nat.cast_one] using hN

theorem gcd_eq_iff_quotient_coprime (D I J : Ideal O) (hD : D ≠ 0)
    (hDI : D ∣ I) (hDJ : D ∣ J) :
    gcd I J = D ↔ IsCoprime (idealQuotient D I) (idealQuotient D J) := by
  have he : gcd I J = D * gcd (idealQuotient D I) (idealQuotient D J) := by
    calc
      gcd I J = gcd (D * idealQuotient D I) (D * idealQuotient D J) := by
        rw [idealQuotient_mul hDI, idealQuotient_mul hDJ]
      _ = _ := by rw [_root_.gcd_mul_left, normalize_eq]
  rw [he, Ideal.isCoprime_iff_gcd]
  constructor
  · intro h
    exact mul_left_cancel₀ hD (h.trans (mul_one D).symm)
  · intro h
    rw [h, mul_one]

def gcdTerm {m n : Type*} (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (i : m) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
      (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) else 0

def gcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, gcdTerm D rows cols a i j k

theorem gcdTerm_eq_quotient {m n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (i : m) (j k : n) :
    gcdTerm D rows cols a i j k =
      (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow D (primaryGenerator (rows i))) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) *
          (quotientMatrix D rows cols i k * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [gcdTerm, totalQuotient, quotientMatrix, ite_eq_left hj, ite_eq_left hk]
      rw [← gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [ite_eq_left hg, ite_eq_left hg, quadraticRow_divisor_factor _ D (hcols j) hj,
          quadraticRow_divisor_factor _ D (hcols k) hk]
        simp only [star_mul]
        ring
      · simp only [ite_eq_right hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [gcdTerm, ite_eq_right hg]
      simp [quotientMatrix, hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [gcdTerm, ite_eq_right hg]
    simp [quotientMatrix, hj]

end CanonicalQuadraticSieve

end

end OAI
