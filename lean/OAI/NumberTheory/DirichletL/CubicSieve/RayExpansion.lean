import OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
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

namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open MixedCrossSeparation (quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos supportIdealFamily_good recoveredSupport firstPassColumnMinus firstPassColumnPlus)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)

def fixedRayExpansion {ι : Type*} (p : ι → O) (F S : Finset ι) : ℂ :=
  ∑ χ : RayCharacter, ∑ η : RayCharacter,
    crossCoeff χ η * supportRay p χ S * supportRay p η F

theorem fixedRayExpansion_eq_cross {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F S : Finset ι) (hd : Disjoint S F) :
    fixedRayExpansion p F S = quadraticCrossPhase p hg S F :=
  (RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc S F hd).symm

def cubeMinusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
    firstPassColumnMinus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ true) S

def cubePlusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
    firstPassColumnPlus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ false) S

def idealPairReindex {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (R : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (h : O) : ℂ :=
  let P := fun i => Ideal.span {p i}
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ R.powerset,
      (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
      star (conjugateIdealRowSum (supportIdealFamily P (R \ D))
        (supportIdealFamily_pos P (R \ D)) (supportIdealFamily_good P hg (R \ D))
        (fun I => star (supportRay p r.1 (recoveredSupport P (R \ D) I)) *
          C₁ (D ∪ recoveredSupport P (R \ D) I)) h) *
      conjugateIdealRowSum (supportIdealFamily P (R \ D))
        (supportIdealFamily_pos P (R \ D)) (supportIdealFamily_good P hg (R \ D))
        (fun I => supportRay p r.2 (recoveredSupport P (R \ D) I) *
          C₂ (D ∪ recoveredSupport P (R \ D) I)) h

theorem threeGaussRowFactor_eq_ray_columns {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h * quadraticCrossPhase p hg N P *
        star (supportMobius (fun i => Ideal.span {p i}) N *
          cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d N *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
        (supportMobius (fun i => Ideal.span {p i}) P *
          cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d P *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h)) := by
  rw [threeGaussRowFactor_eq_transformedPair p hp hcop hg hc hpr N P B hNP hNB hPB]
  unfold cubeTransformedPair cubeMinusCoefficient cubePlusCoefficient
  rw [fixedRayExpansion_eq_cross p hp hcop hg hc (cubeOddSupport B v ε₁ ε₂) N
      (hNB.mono_right (Finset.filter_subset _ _)),
    fixedRayExpansion_eq_cross p hp hcop hg hc (cubeOddSupport B v ε₁ ε₂) P
      (hPB.mono_right (Finset.filter_subset _ _))]
  simp only [star_mul, star_star]
  ring

theorem sum_threeGaussRowFactor_eq_ideal_rows {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (R B : Finset ι) (hRB : Disjoint R B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg R
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d) h := by
  let A := cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d
  let C := cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d
  have hsum :
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        quadraticCrossPhase p hg N P *
          star (supportMobius (fun i => Ideal.span {p i}) N * A N *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
          (supportMobius (fun i => Ideal.span {p i}) P * C P *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h)) else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N hN
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hd : Disjoint N P
    · rw [ite_eq_left hd, ite_eq_left hd,
        threeGaussRowFactor_eq_ray_columns p hp hcop hg hc hpr N P B hd
          (hRB.mono_left (Finset.mem_powerset.mp hN))
          (hRB.mono_left (Finset.mem_powerset.mp hP))]
      dsimp only [A, C]
      ring
    · simp [hd]
  rw [hsum]
  congr 1
  exact FirstCauchyArithmetic.quadratic_phase_reindex_to_ideal_rows p hp hinj hg hc R A C h

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open FourierBridge (logPhase logPhase_norm logPhase_continuous_left)
open EisensteinSchwartzPoisson (paperRadialFourier)

def logTwistMinus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * star (V (y S) * logPhase t (-(y S)))

def logTwistPlus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * (V (y S) * logPhase t (-(y S)))

theorem threeGaussRowFactor_log_twist {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ) (t : ℝ) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h =
    (V₁ (y₁ N) * logPhase t (-(y₁ N))) * (V₂ (y₂ P) * logPhase t (-(y₂ P))) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  simp only [threeGaussRowFactor, logTwistMinus, logTwistPlus, star_mul, star_star]
  ring

theorem integrable_log_pair (b : 𝓢(ℝ, ℂ)) (x y : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ => b t * (logPhase t x * logPhase t y * c)) volume := by
  apply b.integrable.mul_bdd (c := ‖c‖)
  · exact (((logPhase_continuous_left x).mul (logPhase_continuous_left y)).mul_const c).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp only [norm_mul, logPhase_norm, one_mul, le_refl])

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)

def primeProductNorm {ι : Type*} (p : ι → O) (S : Finset ι) : ℝ :=
  ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2

theorem primeProductNorm_pos {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    0 < primeProductNorm p S :=
  pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))) 2

theorem primeProductNorm_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (S T : Finset ι) (hd : Disjoint S T) :
    primeProductNorm p (S ∪ T) = primeProductNorm p S * primeProductNorm p T := by
  simp only [primeProductNorm, Finset.prod_union hd, map_mul, norm_mul, mul_pow]

def columnLog {ι : Type*} (p : ι → O) (X : ℝ) (S : Finset ι) : ℝ :=
  Real.log (primeProductNorm p S / X)

def firstDualScale {ι : Type*} (p : ι → O) (C : Finset ι)
    (lengthScale X₁ X₂ : ℝ) (d h : O) : ℝ :=
  lengthScale * ‖eisEmbedding h‖ ^ 2 /
    (‖eisEmbedding d‖ ^ 2 * primeProductNorm p C * X₁ * X₂)

theorem actual_radial_argument {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (N P C : Finset ι)
    (hNP : Disjoint N P) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (lengthScale X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (d h : O) :
    firstDualScale p C lengthScale X₁ X₂ d h * Real.exp (-(columnLog p X₁ N) - columnLog p X₂ P) =
      lengthScale * ‖eisEmbedding h‖ ^ 2 /
        (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ C)) := by
  rw [primeProductNorm_union p (N ∪ P) C (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    primeProductNorm_union p N P hNP]
  simp only [columnLog, sub_eq_add_neg, Real.exp_add, Real.exp_neg]
  rw [Real.exp_log (div_pos (primeProductNorm_pos p hp N) hX₁),
    Real.exp_log (div_pos (primeProductNorm_pos p hp P) hX₂)]
  simp only [firstDualScale, div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp [ne_of_gt hX₁, ne_of_gt hX₂]

def normalizedColumn {ι : Type*} (p : ι → O) (C : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  C S / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)

theorem threeGaussRowFactor_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (normalizedColumn p C₁) (normalizedColumn p C₂) d h =
    ((‖eisEmbedding (∏ i ∈ N, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ P, p i)‖ : ℂ)⁻¹) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  have hs (x : ℝ) : star (x : ℂ) = (x : ℂ) := by simp
  have hsi (x : ℝ) : star ((x : ℂ)⁻¹) = (x : ℂ)⁻¹ := by simp
  simp only [threeGaussRowFactor, normalizedColumn, div_eq_mul_inv, star_mul, hsi]
  ring

theorem actual_pair_prefactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (lengthScale : ℝ) (d h : O) :
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
        (normalizedColumn p C₁) (normalizedColumn p C₂) d h := by
  rw [threeGaussRowFactor_normalized]
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩), Finset.prod_union hNP]
  simp only [map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem cube_integral_of_radial_separation {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ) (R : ℝ)
    (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
      ∫ t : ℝ, (V₁ x * FourierBridge.logPhase t (-x)) *
        (V₂ y * FourierBridge.logPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h) volume ∧
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
  let G : ℝ → Finset ι → Finset ι → ℂ := fun t N P => if Disjoint N P then
    b t * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0
  have hGint (N P : Finset ι) : Integrable (fun t => G t N P) volume := by
    by_cases hd : Disjoint N P
    · simp only [G, ite_eq_left hd]
      convert integrable_log_pair b (-(y₁ N)) (-(y₂ P))
        (V₁ (y₁ N) * V₂ (y₂ P) * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) using 1
      funext t
      rw [threeGaussRowFactor_log_twist]
      ring
    · simp only [G, ite_eq_right hd]
      exact integrable_zero _ _ _
  have hGsum (t : ℝ) :
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) =
        b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
    calc
      _ = b t * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
          (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0) := by
            simp only [G, Finset.mul_sum, mul_ite, mul_zero]
      _ = _ := by
        rw [sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
        ring
  have hint : Integrable (fun t => ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) volume :=
    integrable_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))
  constructor
  · simpa only [hGsum] using hint
  · have hterm (N P : Finset ι) :
        (if Disjoint N P then
          (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ∫ t : ℝ, G t N P := by
      by_cases hd : Disjoint N P
      · simp only [G, ite_eq_left hd]
        rw [hsep (y₁ N) (y₂ P), ← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [threeGaussRowFactor_log_twist]
        ring
      · simp [G, hd]
    calc
      _ = ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, ∫ t : ℝ, G t N P := by
        apply Finset.sum_congr rfl
        intro N hN
        exact Finset.sum_congr rfl (fun P hP => hterm N P)
      _ = ∫ t : ℝ, ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P := by
        rw [integral_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))]
        apply Finset.sum_congr rfl
        intro N hN
        exact (integral_finsetSum _ (fun P _ => hGint N P)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hGsum t

end FirstPassCubeLabels

namespace QuadraticDivisorSplit
abbrev O := ActualEisensteinCubic.O

theorem exists_unique_split (B C D : Ideal O) (hBC : IsCoprime B C)
    (hD : D ∣ B * C) :
    ∃! x : Ideal O × Ideal O, x.1 ∣ B ∧ x.2 ∣ C ∧ x.1 * x.2 = D := by
  obtain ⟨D₁, D₂, h₁, h₂, hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hD
  refine ⟨(D₁, D₂), ⟨h₁, h₂, hprod.symm⟩, ?_⟩
  intro y hy
  apply Prod.ext
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.mono hy.1 h₂).dvd_of_dvd_mul_right
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_right _ _
    · apply (hBC.mono h₁ hy.2.1).dvd_of_dvd_mul_right
      rw [hy.2.2, hprod]
      exact dvd_mul_right _ _
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.symm.mono hy.2.1 h₁).dvd_of_dvd_mul_left
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_left _ _
    · apply (hBC.symm.mono h₂ hy.1).dvd_of_dvd_mul_left
      rw [hy.2.2, hprod]
      exact dvd_mul_left _ _

theorem split_product_injective (B C : Ideal O) (hBC : IsCoprime B C) :
    Function.Injective (fun x : {x : Ideal O × Ideal O // x.1 ∣ B ∧ x.2 ∣ C} =>
      x.val.1 * x.val.2) := by
  intro x y hxy
  have hD : x.val.1 * x.val.2 ∣ B * C := mul_dvd_mul x.property.1 x.property.2
  obtain ⟨z, hz, huniq⟩ := exists_unique_split B C (x.val.1 * x.val.2) hBC hD
  apply Subtype.ext
  exact (huniq x.val ⟨x.property.1, x.property.2, rfl⟩).trans
    (huniq y.val ⟨y.property.1, y.property.2, hxy.symm⟩).symm

open IdealMobiusDivisorSum

theorem divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) :
    idealDivisors (B * C) =
      ((idealDivisors B) ×ˢ (idealDivisors C)).image (fun x => x.1 * x.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hB hC), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨x, hx, _⟩ := exists_unique_split B C D hBC hD
    exact ⟨x, Finset.mem_product.mpr
      ⟨(mem_idealDivisors hB).mpr hx.1, (mem_idealDivisors hC).mpr hx.2.1⟩, hx.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1)
      ((mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2)

theorem sum_divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors (B * C), f D) =
      ∑ D₁ ∈ idealDivisors B, ∑ D₂ ∈ idealDivisors C, f (D₁ * D₂) := by
  rw [divisors_coprime_product B C hB hC hBC, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy hxy
    have hx' : x.1 ∣ B ∧ x.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2⟩
    have hy' : y.1 ∣ B ∧ y.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hy).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hy).2⟩
    have he : (⟨x, hx'⟩ : {z : Ideal O × Ideal O // z.1 ∣ B ∧ z.2 ∣ C}) = ⟨y, hy'⟩ :=
      split_product_injective B C hBC hxy
    exact congrArg Subtype.val he

end QuadraticDivisorSplit

end

end OAI
