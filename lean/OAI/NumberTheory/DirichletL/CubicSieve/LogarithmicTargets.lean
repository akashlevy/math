import OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity
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
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_remainder_bound (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (x : SecondExpansionData ι) (hx : x ∈ secondSupportedSector p F K R X M) :
    primeProductNorm p R ≤ X*Real.exp M := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have h := (secondSourceSupport_bounds p hp X M x hs hE).1
  rw [← hr]
  exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans h

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_eq_empty (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hR : ¬ primeProductNorm p R ≤ X*Real.exp M) :
    secondSupportedSector p F K R X M = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hR (secondSupportedSector_remainder_bound p hp F R K X M x hx)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem truncatedSecondSource_eq_binned
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (D F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g W : 𝓢(ℝ,ℂ))
    (X Y M Kmax : ℝ) (hX : 0 < X) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) :
    let H := fun S => normalizedColumn p (fun A => g (columnLog p X A)) S
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondZero p hg F Ψ m c d H W Y K +
        ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
          ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            secondExpansionSource p hp hcop hg F Ψ m c d z
              (secondLogSector p D F K R X M j) H H W Y := by
  dsimp only
  rw [truncatedSecondSource_eq_nonzero_add_zero, add_comm,
    truncatedSecondSource_eq_fixed_sectors p hp hcop hg hinj hc hpr]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  simp only [boundedPrimeSupports, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro R hR
  have hE : ∀ x ∈ secondExpansionSector F (fun G E => (K G E).erase 0) R,
      x.divisor ⊆ x.sourceCommon := by
    intro x hx
    exact ((mem_secondExpansionPool _ _ _).mp (Finset.mem_filter.mp hx).1).2.1
  have hs := secondExpansionSource_eq_supported p hp hcop hg hinj F Ψ m c d z
    g W X Y M hX hgM (secondExpansionSector F (fun G E => (K G E).erase 0) R) hE
  rw [hs]
  change secondExpansionSource p hp hcop hg F Ψ m c d z (secondSupportedSector p F K R X M)
      _ _ W Y = _
  by_cases hNR : primeProductNorm p R ≤ X*Real.exp M
  · rw [ite_eq_left hNR]
    simp only [secondExpansionSource]
    exact (sum_secondLogSector p hp D F K R X M Kmax (hK R hR) _).symm
  · rw [ite_eq_right hNR, secondSupportedSector_eq_empty p hp F R K X M hNR]
    simp only [secondExpansionSource, Finset.sum_empty]

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

lemma supported_cutoff_denominator (E G U : ℝ) (hE : E ≤ G) (hG : 1 ≤ G) :
    E * (U/G)^2 ≤ U^2 := by
  have hG0 : 0 < G := by linarith
  have hEG : E ≤ G^2 := by nlinarith
  have he : E/G^2 ≤ 1 := (div_le_one (sq_pos_of_pos hG0)).mpr hEG
  calc
    E*(U/G)^2 = U^2*(E/G^2) := by ring
    _ ≤ U^2*1 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := mul_one _

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm jLabel b0Label)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open SecondPassIntegration (densityChildEnergy)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

end SecondPassArithmetic

namespace CubicEisenstein

def smoothFirstCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*s*(rowLogD (embeddedRow r) p j:ℂ)
def smoothSecondCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*(s^2*(rowLogD (embeddedRow r) p j:ℂ)^2+s*(rowLogDD (embeddedRow r) p j:ℂ))

lemma smoothFirstCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothFirstCoefficient s r j p=deriv (axisSlice (smoothSummand s r) p j) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothFirstCoefficient smoothSummand
  ring

lemma smoothSecondCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSecondCoefficient s r j p=deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field',deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothSecondCoefficient smoothSummand
  ring

end CubicEisenstein

namespace CubicEisenstein

lemma spatial_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ∃ U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧
      ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀q∈U, 0<q 2 ∧ ∀r : CuspCosets,
        ‖smoothSummand s r q‖≤M₀ r ∧ ∀j : Fin 3,
        ‖smoothFirstCoefficient s r j q‖≤M₁ r ∧
        ‖smoothSecondCoefficient s r j q‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := clampedCoordinates deltaLoss hδ
  let C := rowBound (coordinateSection (path p))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path p))]
  let U : Set SpatialCoordinates := {q | deltaLoss<q 2 ∧ rowBound (coordinateSection (path q))<C}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 2)).inter
    (isOpen_lt (continuous_coordinate_rowBound.comp (continuous_clampedCoordinates deltaLoss hδ)) continuous_const)
  have hpU : p∈U := by constructor <;> dsimp [deltaLoss,C] <;> linarith
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨U,hU,hpU,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro q hq
  have hpos : 0<q 2 := lt_trans hδ hq.1
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r q‖≤M r := by
    rw [smoothSummand_eq_clamped s r q deltaLoss hδ hq.1.le]
    exact hbound (path q,s) hq.2.le le_rfl le_rfl r
  have hfrac : 1 / q 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hq.1.le
  have hfrac₂ : 7 / (q 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith [hq.1]
  refine ⟨hm,fun j => ?_⟩
  rw [smoothFirstCoefficient_eq_deriv _ _ _ _ hpos,smoothSecondCoefficient_eq_deriv _ _ _ _ hpos]
  constructor
  · apply (norm_smooth_axis_deriv s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply (norm_smooth_axis_deriv2 s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

end CubicEisenstein

end

end OAI
