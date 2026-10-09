import OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
import OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
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

namespace EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT

open QuadraticInitialBound

theorem paperRadialFourier_nonzero_sum_uniform (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    K * ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
      pvControl W := by
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  have he : (∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)) =
      ∑' h : {h : O // h ≠ 0}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [ite_eq_right h.property]
  rw [he]
  exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hs.subtype _)) hK.le).trans
    (pv_lattice_bound W K hK)

theorem maskedPrincipalRemainder_uniform {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖maskedPrincipalRemainder P S W M‖ ≤ (2 : ℝ) ^ S.card * pvControl W := by
  let n := fun E : Finset α => (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)
  have hn (E : Finset α) : 0 < n E := by
    dsimp [n]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  let f := fun E : Finset α =>
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)
  have hf (E : Finset α) : M * ‖f E‖ ≤ pvControl W := by
    have ht := paperRadialFourier_nonzero_sum_uniform W (M / n E) (div_pos hM (hn E))
    have he (h : O) : M / n E * ‖eisEmbedding h‖ ^ 2 = M * ‖eisEmbedding h‖ ^ 2 / n E := by ring
    simp only [he] at ht
    have hm := norm_ideal_moebius_le_one (∏ i ∈ E, P i)
    dsimp only [f]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    calc
      _ = ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ((M / n E) * ‖∑' h : O, if h = 0 then 0 else
            paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)‖) := by dsimp [n]; ring
      _ ≤ 1 * pvControl W := mul_le_mul hm ht (by positivity) zero_le_one
      _ = _ := one_mul _
  change ‖(M : ℂ) * ∑ E ∈ S.powerset, f E‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * ∑ E ∈ S.powerset, ‖f E‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM.le
    _ = ∑ E ∈ S.powerset, M * ‖f E‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ E ∈ S.powerset, pvControl W := Finset.sum_le_sum (fun E _ => hf E)
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end EisensteinSchwartzPoisson

namespace FirstPassCubeLabels
open ActualEisensteinCubic MixedCrossSeparation FirstCauchyArithmetic RayFourExpansion

theorem supportRay_star {ι : Type*} (p : ι → ActualEisensteinCubic.O) (χ : RayCharacter) (S : Finset ι) :
    supportRay p (star χ) S = star (supportRay p χ S) := by
  simp only [supportRay, rayCharacter, MulChar.star_apply]

theorem supportRay_mul {ι : Type*} (p : ι → ActualEisensteinCubic.O) (χ η : RayCharacter) (S : Finset ι) :
    supportRay p (χ * η) S = supportRay p χ S * supportRay p η S := by
  simp only [supportRay, rayCharacter, MulChar.mul_apply]

theorem columnG_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnG p hp hcop hg S = ∑ χ : RayCharacter, gCoeff χ * supportRay p χ S := by
  have h := canonicalProductG_character_expansion (fun i : S => p i.val)
    (fun i => hp i.val) (columnPrimeCoprime p hcop S) (fun i => hg i.val)
    (fun i => hc i.val) (fun i => hpr i.val)
  simpa only [columnG, supportRay, Finset.prod_coe_sort] using h

def coreRayCharacter (negative : Bool) (χ ξ : RayCharacter) : RayCharacter :=
  (if negative then star χ else χ) * ξ

def coreRayCoefficient {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) : ℂ :=
  (if negative then star (crossCoeff χ η * supportRay p η F)
    else crossCoeff χ η * supportRay p η F) * gCoeff ξ

theorem core_phase_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F S : Finset ι) (negative : Bool) :
    (if negative then star (fixedRayExpansion p F S) else fixedRayExpansion p F S) *
        columnG p hp hcop hg S =
      ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        coreRayCoefficient p F negative χ η ξ * supportRay p (coreRayCharacter negative χ ξ) S := by
  rw [columnG_ray_expansion p hp hcop hg hc hpr S]
  cases negative <;> simp only [Bool.false_eq_true,  ite_false, ite_true,
    fixedRayExpansion, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
    coreRayCoefficient, coreRayCharacter, supportRay_mul, supportRay_star]
  · conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro ξ _
    ring
  · conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro ξ _
    ring

theorem coreRayCoefficient_norm_le {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) :
    ‖coreRayCoefficient p F negative χ η ξ‖ ≤ ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
  have hη : ‖supportRay p η F‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one η _
  have hmul : ‖crossCoeff χ η‖ * ‖supportRay p η F‖ ≤ ‖crossCoeff χ η‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hη
  cases negative <;> simp only [coreRayCoefficient, Bool.false_eq_true,
    ite_false, ite_true, norm_mul, norm_star]
  all_goals exact mul_le_mul_of_nonneg_right hmul (norm_nonneg _)

theorem coreRayCoefficient_mass {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
      ‖coreRayCoefficient p F negative χ η ξ‖) ≤ 32 * 512 := by
  calc
    _ ≤ ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
      gcongr with χ _ η _ ξ _
      exact coreRayCoefficient_norm_le p F negative χ η ξ
    _ = (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ ξ : RayCharacter, ‖gCoeff ξ‖) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ 512 * 32 := mul_le_mul crossCoeff_sum_norm_le gCoeff_sum_norm_le (by positivity) (by norm_num)
    _ = 32 * 512 := by ring

def coreRayTwist (negative : Bool) (χ ξ : RayCharacter) : ActualEisensteinCubic.O →* ℂ where
  toFun a := rayCharacter (coreRayCharacter negative χ ξ) a
  map_one' := by simp [rayCharacter]
  map_mul' a b := rayCharacter_mul _ a b

@[simp] theorem coreRayTwist_prod {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (S : Finset ι) (negative : Bool) (χ ξ : RayCharacter) :
    coreRayTwist negative χ ξ (∏ i ∈ S, p i) =
      supportRay p (coreRayCharacter negative χ ξ) S := rfl

@[simp] theorem twisted_core_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (negative : Bool) (χ ξ : RayCharacter) :
    (Ψ * coreRayTwist negative χ ξ) (∏ i ∈ S, p i) =
      Ψ (∏ i ∈ S, p i) * supportRay p (coreRayCharacter negative χ ξ) S := rfl

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)

section FixedColumn
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
  (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
  (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)

def dilatedCoreRow (t : ℝ) (z : O) : ℂ :=
  dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
    negative χ p B v ε₁ ε₂ c d z

private theorem cubeCoreCoefficient_continuous (S : Finset ι) :
    Continuous (fun t : ℝ => cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S) := by
  cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    have h := FourierBridge.logPhase_continuous_left (-(y S))
    fun_prop

private theorem norm_cubeCoreCoefficient (S : Finset ι) (t : ℝ) :
    ‖cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S‖ =
      ‖cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y 0 S‖ := by
  cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true,
    norm_mul, norm_star, FourierBridge.logPhase_norm]

theorem dilatedCoreRow_continuous (z : O) :
    Continuous (fun t : ℝ => dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z) := by
  unfold dilatedCoreRow dilatedRayColumn supportConjugateSum
  apply continuous_finsetSum
  intro U hU
  have h := cubeCoreCoefficient_continuous p hp hcop hg B v ε₁ ε₂ negative C V y (D ∪ U)
  fun_prop

theorem dilatedCoreRow_uniform_bound (z : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ≤ M := by
  let q := fun (t : ℝ) (U : Finset ι) =>
    FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) U *
      ((if negative then star (FirstCauchyArithmetic.supportRay p χ U)
        else FirstCauchyArithmetic.supportRay p χ U) *
        cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t (D ∪ U) *
        afterDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ c d U) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z)
  refine ⟨∑ U ∈ (F \ D).powerset, ‖q 0 U‖, by positivity, ?_⟩
  intro t
  change ‖∑ U ∈ (F \ D).powerset, q t U‖ ≤ _
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro U hU
  simp only [q, norm_mul, norm_cubeCoreCoefficient]

theorem dilatedCoreRow_integrable (z : O) {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t : ℝ => k t *
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ^ 2) volume := by
  obtain ⟨M, hM, hb⟩ := dilatedCoreRow_uniform_bound p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d z
  apply hk.mul_bdd (c := M ^ 2)
  · exact ((dilatedCoreRow_continuous p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d z).norm.pow 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2)
end FixedColumn

def firstRayIntegrand {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d f h : O) (b : 𝓢(ℝ, ℂ)) (t : ℝ) : ℝ :=
  ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ * ‖rayPairWeight p r D h‖ *
    ‖rayIdealRow p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d)
      negative (if negative then r.1 else r.2) D h‖ ^ 2

theorem firstRayIntegrand_integrable {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    Integrable (firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d f h b) volume := by
  have hi := dilatedCoreRow_integrable p hp hcop hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) C V y c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂)
    b.integrable.norm
  convert hi.mul_const (‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ * ‖rayPairWeight p r D h‖ *
    ‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D‖ ^ 2) using 1
  funext t
  simp only [firstRayIntegrand, rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv,
    norm_mul, mul_pow, dilatedCoreRow]
  ring

theorem first_ray_energy_integral (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ)
      (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ)
      (b : Ideal O × O → 𝓢(ℝ, ℂ)) (J : ℕ) (M H Y : ℝ),
      0 ≤ M → 0 ≤ H → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t) →
      (∑ x ∈ s, ‖w x‖ * ∫ t : ℝ,
        firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d
          (ConcretePrimeRowBridge.idealGenerator x.1) x.2 (b x) t) ≤
      (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) *
        ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C V y c d t z‖ ^ 2 := by
  obtain ⟨K, hK, hpoint⟩ := first_cube_energy_small_power deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc F D B v ε₁ ε₂ hv negative r C V y c d s T w b J M H Y hM hH hY hs hmap hT hnorm hw hdom
  let Ψ := fun t z => dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) C V y c d t z
  let source := fun t : ℝ => ∑ x ∈ s, ‖w x‖ *
    firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d
      (ConcretePrimeRowBridge.idealGenerator x.1) x.2 (b x) t
  let target := fun t : ℝ => firstLogDensity J t * ∑ z ∈ T, ‖Ψ t z‖ ^ 2
  have isource : Integrable source volume := by
    apply integrable_finsetSum
    intro x hx
    exact (firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖
  have itarget : Integrable target volume := by
    simp only [target, Finset.mul_sum]
    exact integrable_finsetSum _ (fun z hz =>
      dilatedCoreRow_integrable p hp hcop hg F D B v ε₁ ε₂ negative
        (if negative then r.1 else r.2) C V y c d z (firstLogDensity_integrable J))
  have hst (t : ℝ) : source t ≤ (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) * target t := by
    let wt := fun x : Ideal O × O => w x * (b x t) *
      cubeBaseFactor p hp hg B v ε₁ ε₂ d x.2 * rayPairWeight p r D x.2
    have hwt (x) (hx : x ∈ s) : ‖wt x‖ ≤ M * H * firstLogDensity J t * ‖crossCoeff r.1 r.2‖ := by
      simp only [wt, norm_mul]
      calc
        _ ≤ M * (H * firstLogDensity J t) * 1 * ‖crossCoeff r.1 r.2‖ := by
          have hden := firstLogDensity_nonneg J t
          gcongr <;> first
            | positivity
            | exact hw x hx
            | exact hdom x hx t
            | exact cubeBaseFactor_norm_le_one p hp hcop hg hc B v ε₁ ε₂ d x.2
            | exact rayPairWeight_norm_le p hinj hc r D x.2
        _ = _ := by ring
    have hh := hpoint p hp hinj hcop hg F D B v ε₁ ε₂ hv negative
      (if negative then r.1 else r.2) C V y t c d s T wt
      (M * H * firstLogDensity J t * ‖crossCoeff r.1 r.2‖) Y
      (by exact mul_nonneg (mul_nonneg (mul_nonneg hM hH) (firstLogDensity_nonneg J t)) (norm_nonneg _))
      hY hs hmap hT hnorm hwt
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [firstRayIntegrand, wt, norm_mul]
      ring
    · dsimp only [target, Ψ, dilatedCoreRow]
      ring
  calc
    _ = ∫ t : ℝ, source t := by
      rw [integral_finsetSum _ (fun x hx =>
        (firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖)]
      exact Finset.sum_congr rfl (fun x hx => (integral_const_mul _ _).symm)
    _ ≤ ∫ t : ℝ, (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) * target t :=
      integral_mono isource (itarget.const_mul _) hst
    _ = _ := integral_const_mul _ _

end FirstPassCubeLabels

end

end OAI
