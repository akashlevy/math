import OAI.NumberTheory.DirichletL.QuadraticSieve.SquareParts
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

theorem second_common_support_reconstruct {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (E G G' : Finset ι) (hEG : E ⊆ G) (hEG' : E ⊆ G')
    (hr : Ideal.span {secondMaskQuotient p E G hEG} =
      Ideal.span {secondMaskQuotient p E G' hEG'}) : G = G' := by
  apply FirstCauchyArithmetic.family_product_injective (fun i => Ideal.span {p i}) hinj
  have hprod (A : Finset ι) (hEA : E ⊆ A) :
      (∏ i ∈ A, (Ideal.span {p i} : Ideal O)) =
        (∏ i ∈ E, Ideal.span {p i}) * Ideal.span {secondMaskQuotient p E A hEA} := by
    rw [secondMaskQuotient_span]
    simpa only [mul_comm] using (Finset.prod_sdiff (f := fun i => (Ideal.span {p i} : Ideal O)) hEA).symm
  change (∏ i ∈ G, (Ideal.span {p i} : Ideal O)) = ∏ i ∈ G', Ideal.span {p i}
  rw [hprod G hEG, hprod G' hEG', hr]

open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondSourcePairKernel (e k : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (S T : Finset ι) : ℂ :=
  (star (H₁ S) * H₂ T /
    ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ) * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ))) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * (primeProductNorm p S * primeProductNorm p T)))

theorem secondFrequencyKernel_eq_kernelPair (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondSourcePairKernel p e k H₁ H₂ W Y) := by
  unfold secondFrequencyKernel secondKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, secondSourcePairKernel]
    rw [secondGaussTerm_test_factors, Finset.prod_union hd, map_mul, norm_mul,
      Complex.ofReal_mul, FirstPassCubeLabels.primeProductNorm_union p S T hd]
    ring
  · simp [hd]

theorem secondFrequencyKernel_eq_child_sectors
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) (secondSourcePairKernel p e k H₁ H₂ W Y) := by
  rw [secondFrequencyKernel_eq_kernelPair,
    secondKernelPair_eq_children p hp hcop hg hinj hc hpr]

def secondSourceCommonCoefficient (Ψ : O →* ℂ) (m c d : O) (G E : Finset ι) : ℂ :=
  (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ))

def truncatedSecondSource (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑ k ∈ K G E.val,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      secondFrequencyKernel p hp hg hinj F Ψ Ψ m
        (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
        (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

def secondSourceTail (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      ∑' k : {k : O // k ∉ K G E.val},
        secondFrequencyKernel p hp hg hinj F Ψ Ψ m
          (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k.val
          (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

theorem inputConjugateRow_eq_truncated_add_tail
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset ι → Finset ι → Finset O) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K +
        secondSourceTail p hp hg hinj F Ψ m c d H W Y K := by
  rw [inputConjugateRow_smoothed_frequency_blocks p hp hg hinj hc F Ψ m c d H W Y hY]
  unfold truncatedSecondSource secondSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G hG
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hs : Summable (fun k : O => secondFrequencyKernel p hp hg hinj F Ψ Ψ m
      (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y) := by
    simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
      (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => H (G ∪ U)) (fun U => H (G ∪ U))]
    exact residualSecondMode_summable p hp hg hinj F G Ψ Ψ m c d
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)
      (primeSubsetGenerator_ne_zero _ _) W Y hY
  rw [← hs.sum_add_tsum_subtype_compl (K G E.val)]
  simp only [secondSourceCommonCoefficient, mul_add, Finset.mul_sum]
  ring_nf

theorem truncatedSecondSource_eq_child_sectors
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ G ∈ F.powerset, ∑ E : G.powerset,
        ∑ z : SecondRayIndex, ∑ V ∈ F.powerset, ∑ k ∈ K G E.val,
          ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d G E.val *
            secondTotalWeight p hp hcop hg Ψ Ψ m
              (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
              (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k (z,V)) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ z) (secondRayPlus Ψ z)
            m (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k (-k)
            (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
              (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y) := by
  unfold truncatedSecondSource
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro E hE
  simp_rw [secondFrequencyKernel_eq_child_sectors p hp hg hinj hcop hc hpr]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro k hk
  ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

@[ext] structure SecondExpansionData (ι : Type*) where
  sourceCommon : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def InSecondQuotientSector (r : O) (x : SecondExpansionData ι) : Prop :=
  ∃ h : x.divisor ⊆ x.sourceCommon,
    Ideal.span {secondMaskQuotient p x.divisor x.sourceCommon h} = Ideal.span {r}

def expansionSupportData (C D : Finset ι) (x : SecondExpansionData ι) : SecondSupportData ι where
  common := C
  firstDivisor := D
  secondDivisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency

theorem expansionSupportData_injOn
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (C D : Finset ι) (r : O) :
    Set.InjOn (expansionSupportData (ι := ι) C D) {x | InSecondQuotientSector p r x} := by
  intro x hx y hy h
  obtain ⟨hxE, hxr⟩ := hx
  obtain ⟨hyE, hyr⟩ := hy
  have he := congrArg SecondSupportData.secondDivisor h
  have hv := congrArg SecondSupportData.overlap h
  have hk := congrArg SecondSupportData.frequency h
  change x.divisor = y.divisor at he
  change x.overlap = y.overlap at hv
  change x.frequency = y.frequency at hk
  have hg : x.sourceCommon = y.sourceCommon := by
    cases x with
    | mk G E V k =>
      cases y with
      | mk G' E' V' k' =>
        dsimp only at he hxE hyE hxr hyr ⊢
        subst E'
        exact second_common_support_reconstruct p hinj E G G' hxE hyE (hxr.trans hyr.symm)
  exact SecondExpansionData.ext hg he hv hk

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_quotient_sector (E G : Finset ι) (hEG : E ⊆ G) (r : O)
    (hr : Ideal.span {secondMaskQuotient p E G hEG} = Ideal.span {r}) :
    primeProductNorm p G =
      ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
        ‖eisEmbedding r‖ ^ 2 := by
  unfold primeProductNorm
  rw [secondMaskQuotient_spec p E G hEG, map_mul, norm_mul, mul_pow]
  congr 1
  rw [eisEmbedding_norm_sq_eq_absNorm_span, eisEmbedding_norm_sq_eq_absNorm_span, hr]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem residual_scale_quotient_sector (X : ℝ) (E G : Finset ι) (hEG : E ⊆ G) (r : O)
    (hr : Ideal.span {secondMaskQuotient p E G hEG} = Ideal.span {r}) :
    X / primeProductNorm p G = X /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
        ‖eisEmbedding r‖ ^ 2) := by
  rw [primeProductNorm_quotient_sector p E G hEG r hr]

end

theorem rowCoprimeMask_eq_of_span_eq {ι : Type*} (P : ι → Ideal O)
    (S : Finset ι) {a b : O} (hab : Ideal.span {a} = Ideal.span {b}) :
    rowCoprimeMask P S a = rowCoprimeMask P S b := by
  have hm (i : ι) : a ∈ P i ↔ b ∈ P i := by
    rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.span_singleton_le_iff_mem, hab]
  simp only [rowCoprimeMask, hm]

theorem rowCoprimeMask_mul_eq_of_span_eq {ι : Type*} (P : ι → Ideal O)
    (S : Finset ι) (m : O) {a b : O} (hab : Ideal.span {a} = Ideal.span {b}) :
    rowCoprimeMask P S (m*a) = rowCoprimeMask P S (m*b) := by
  apply rowCoprimeMask_eq_of_span_eq P S
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton, hab]

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic FirstPassCubeLabels
open SecondPassArithmetic (SecondSupportData secondSectorZ)

end SecondPassIntegration

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (elementNorm)

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label firstLogDensity)
open SecondPassIntegration (childGeometricMean)
open JointLogSeparation

theorem outerWindow_global_bound (windows : Fin 7 → ℝ → ℂ)
    (hc : ∀ j, HasCompactSupport (windows j)) (hs : ∀ j, Continuous (windows j)) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ z ud ue uv kap : ℝ,
      ‖outerWindow windows z ud ue uv kap‖ ≤ Cw := by
  have hb (j : Fin 7) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖windows j x‖ ≤ B := by
    obtain ⟨B,hB⟩ := ((hc j).isCompact_range (hs j)).bddAbove_image continuous_norm.continuousOn
    have he (x : ℝ) : ‖windows j x‖ ≤ B := hB ⟨windows j x, ⟨x,rfl⟩,rfl⟩
    exact ⟨B,(norm_nonneg _).trans (he 0),he⟩
  choose B hB hbound using hb
  have h0 := hB 0
  have h1 := hB 1
  have h2 := hB 2
  have h3 := hB 3
  have h4 := hB 4
  refine ⟨B 0 * B 1 * B 2 * B 3 * B 4, by positivity, ?_⟩
  intro z ud ue uv kap
  simp only [outerWindow, norm_mul]
  gcongr
  all_goals first | positivity | apply hbound

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open JointLogSeparation (halfNormalizationCLM)
open SecondPassIntegration (normalizedColumn_pair_extract_fixed_profiles conjugateProfile)

theorem secondSourcePairKernel_normalized_shift {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G S T : Finset ι)
    (hGS : Disjoint G S) (hGT : Disjoint G T)
    (e k : O) (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    secondSourcePairKernel p e k
      (fun A => normalizedColumn p (fun B => g₁ (columnLog p X B)) (G∪A))
      (fun A => normalizedColumn p (fun B => g₂ (columnLog p X B)) (G∪A)) W Y S T =
      (X : ℂ)⁻¹ * radialPairKernel p e k W
        (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
        (X / primeProductNorm p G) (X / primeProductNorm p G) Y S T := by
  unfold secondSourcePairKernel
  rw [normalizedColumn_pair_extract_fixed_profiles p hp G S T hGS hGT X hX U hUc hUs
    g₁ g₂ hU₁ hU₂]
  simp only [radialPairKernel, normalizedColumn, SecondPassIntegration.conjugateProfile_apply,
     Complex.star_def, Complex.conj_ofReal, div_eq_mul_inv,
     mul_inv_rev, map_inv₀, map_mul]
  ring_nf

end SecondPassArithmetic

namespace UnrestrictedIdealReindex
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open PrimaryIdealUnitReindex CanonicalQuadraticSieve

abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}
abbrev NonzeroElement := {z : O // z ≠ 0}

theorem span_unit_generator (u : Oˣ) (I : NonzeroIdeal) :
    Ideal.span {u.val * idealGenerator I.val} = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, span_idealGenerator]

def unitIdealToElement (p : Oˣ × NonzeroIdeal) : NonzeroElement :=
  ⟨p.1.val * idealGenerator p.2.val, mul_ne_zero p.1.ne_zero (idealGenerator_ne_zero p.2.val p.2.property)⟩

theorem unitIdealToElement_bijective : Function.Bijective unitIdealToElement := by
  constructor
  · intro p q hpq
    have he : p.1.val * idealGenerator p.2.val = q.1.val * idealGenerator q.2.val := congrArg Subtype.val hpq
    have hi : p.2 = q.2 := by
      apply Subtype.ext
      simpa only [span_unit_generator] using congrArg (fun z : O => Ideal.span {z}) he
    have hu : p.1 = q.1 := by
      apply Units.ext
      rw [hi] at he
      exact mul_right_cancel₀ (idealGenerator_ne_zero q.2.val q.2.property) he
    exact Prod.ext hu hi
  · intro z
    let I : NonzeroIdeal := ⟨Ideal.span {z.val}, Ideal.span_singleton_eq_bot.not.mpr z.property⟩
    have ha : Associated (idealGenerator I.val) z.val :=
      Ideal.span_singleton_eq_span_singleton.mp (span_idealGenerator I.val)
    obtain ⟨u, hu⟩ := ha
    refine ⟨(u, I), Subtype.ext ?_⟩
    change u.val * idealGenerator I.val = z.val
    simpa only [mul_comm] using hu

def unitIdealEquiv : Oˣ × NonzeroIdeal ≃ NonzeroElement :=
  Equiv.ofBijective unitIdealToElement unitIdealToElement_bijective

theorem tsum_nonzero_unit_invariant (f : O → ℂ) (hf : Summable f)
    (hu : ∀ (u : Oˣ) (z : O), f (u.val * z) = f z) :
    (∑' z : NonzeroElement, f z.val) = (6 : ℂ) * ∑' I : NonzeroIdeal, f (idealGenerator I.val) := by
  let : Finite Oˣ := finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  have he : (∑' z : NonzeroElement, f z.val) =
      ∑' p : Oˣ × NonzeroIdeal, f (p.1.val * idealGenerator p.2.val) :=
    (unitIdealEquiv.tsum_eq (fun z : NonzeroElement => f z.val)).symm
  have hs : Summable (fun p : Oˣ × NonzeroIdeal => f (p.1.val * idealGenerator p.2.val)) :=
    unitIdealEquiv.summable_iff.mpr (hf.subtype _)
  rw [he, hs.tsum_prod]
  simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card Oˣ = 6 := by simpa only [Nat.card_eq_fintype_card] using card_units_eq_six
  rw [hc]
  norm_num

theorem tsum_unit_invariant_of_zero (f : O → ℂ) (hf : Summable f) (h0 : f 0 = 0)
    (hu : ∀ (u : Oˣ) (z : O), f (u.val * z) = f z) :
    (∑' z : O, f z) = (6 : ℂ) * ∑' I : NonzeroIdeal, f (idealGenerator I.val) := by
  have he : (∑' z : NonzeroElement, f z.val) = ∑' z : O, f z := by
    apply tsum_subtype_eq_of_support_subset
    intro z hz
    exact fun hz0 => hz (hz0 ▸ h0)
  rw [← he]
  exact tsum_nonzero_unit_invariant f hf hu

end UnrestrictedIdealReindex

end

end OAI
