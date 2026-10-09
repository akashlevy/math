import OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicLoss
import OAI.NumberTheory.DirichletL.CubicSieve.PooledRows
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

namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open MixedCrossSeparation (columnCoefficient)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def inputColumn (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*H S

end InitialMeanSquare

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

instance fullSLContinuousAction : ContinuousConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨continuous_hyperbolic_action⟩

instance hyperbolicVolume_fullSupport : Measure.IsOpenPosMeasure hyperbolicVolume where
  open_pos U hU hne := by
    obtain ⟨u,hu⟩ := hne
    have hcover : (Set.univ : Set HyperbolicSpace) ⊆ ⋃g:SL(2,ℂ),g • U := by
      intro w hw
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(2,ℂ)) u w
      exact Set.mem_iUnion.mpr ⟨g,u,hu,hg⟩
    obtain ⟨seq,hseq⟩ := isLindelof_univ.indexed_countable_subcover
      (fun g : SL(2,ℂ) => g • U) (fun g => isOpenMap_smul g U hU) hcover
    intro hzero
    have hz : hyperbolicVolume (⋃n:ℕ,seq n • U)=0 := by
      apply measure_iUnion_null
      intro n
      rw [measure_smul,hzero]
    have htotal : hyperbolicVolume Set.univ=0 := measure_mono_null hseq hz
    exact hyperbolicVolume_ne_zero (Measure.measure_univ_eq_zero.mp htotal)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_upper_triangular_height (M : SL(2,O)) (hc : M 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix M • upperPoint z v hv)=v := by
  have hdet : M 0 0*M 1 1=1 := by
    have h := M.property
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using h
  let u : Oˣ := ⟨M 1 1,M 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (M 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [hyperbolicHeight_action_upperPoint]
  simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
    hn,one_pow,]
  norm_num

def hyperbolicSpatialCoordinates (w : HyperbolicSpace) : SpatialCoordinates :=
  ![(hyperbolicHorizontal w).re,(hyperbolicHorizontal w).im,hyperbolicHeight w]

lemma hyperbolicSpatialCoordinates_continuous : Continuous hyperbolicSpatialCoordinates := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact Complex.continuous_re.comp hyperbolicHorizontal_continuous
  · exact Complex.continuous_im.comp hyperbolicHorizontal_continuous
  · exact hyperbolicHeight_continuous

lemma hyperbolicSpatialCoordinates_positive (w : HyperbolicSpace) :
    0<hyperbolicSpatialCoordinates w 2 := hyperbolicHeight_pos w

lemma hyperbolicSpatialCoordinates_reconstruct (w : HyperbolicSpace) :
    upperPoint ((hyperbolicSpatialCoordinates w 0:ℂ)+(hyperbolicSpatialCoordinates w 1:ℂ)*Complex.I)
      (hyperbolicSpatialCoordinates w 2) (hyperbolicSpatialCoordinates_positive w)=w := by
  change upperPoint (((hyperbolicHorizontal w).re:ℂ)+((hyperbolicHorizontal w).im:ℂ)*Complex.I)
    (hyperbolicHeight w) (hyperbolicHeight_pos w)=w
  rw [Complex.re_add_im]
  exact upperCoordinates_right_inverse w

end CubicEisenstein

namespace SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem globalChildBudget_height (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε t K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side =
      ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*
        globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp only [globalChildBudget,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro q hq
  simp only [globalDescentWeight,norm_zero,add_zero,one_pow,mul_one]
  ring

def globalFirstFiniteEnergy (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (t : ℝ) : ℝ :=
  ∑ b∈s,w b*∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2

theorem globalFirstFiniteEnergy_integrable (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (J : ℕ) :
    Integrable (fun t => firstLogDensity J t*globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t) := by
  simp only [globalFirstFiniteEnergy,Finset.mul_sum]
  apply integrable_finsetSum
  intro b hb
  apply integrable_finsetSum
  intro z hz
  have hi := firstCoreInputRow_integrable p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (FirstPassCubeLabels.normalizedColumn p
      (fun A => g (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r z
    (FirstPassCubeLabels.firstLogDensity_integrable J)
  simpa only [globalFirstCoreRow,mul_left_comm] using hi.const_mul (w b)

end SecondPassArithmetic

namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

theorem finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤256*(columnDyadicLength H+1:ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑I∈divisorDyadicBin S H j,1/(Ideal.absNorm I:ℝ))≤256 := by
    have hp : 0<(2:ℝ)^j.val := by positivity
    have hone : 1≤(2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card:ℝ)≤128*(2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I∈divisorDyadicBin S H j) :
        1/(Ideal.absNorm I:ℝ)≤2/(2:ℝ)^j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith
    calc
      _ ≤ ∑_I∈divisorDyadicBin S H j,2/(2:ℝ)^j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card:ℝ)*(2/(2:ℝ)^j.val) := by simp
      _ ≤ (128*(2:ℝ)^j.val)*(2/(2:ℝ)^j.val) := by gcongr
      _ = _ := by field_simp; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑j : Fin (columnDyadicLength H+1),(256:ℝ) := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring

theorem ideal_reciprocal_cauchy (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (v : Ideal O → ℂ) :
    ‖∑I∈S,v I‖^2≤(∑I∈S,1/(Ideal.absNorm I:ℝ))*
      (∑I∈S,(Ideal.absNorm I:ℝ)*‖v I‖^2) := by
  have hpos (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S v) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun I hI => by positivity) (fun I hI => by positivity)
  intro I hI
  exact le_of_eq (by field_simp [(hpos I hI).ne'])

open CompletedGauss QuadraticSquarefreeKernel

def columnSquareFiber (S : Finset (Ideal O)) (A : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => squarePart I=A)

theorem columnSquareFiber_injective (S : Finset (Ideal O)) (A : Ideal O) :
    Function.Injective (fun I : columnSquareFiber S A => squarefreePart I.val) := by
  intro I J he
  change squarefreePart I.val=squarefreePart J.val at he
  apply Subtype.ext
  have hi := (Finset.mem_filter.mp I.property).2
  have hj := (Finset.mem_filter.mp J.property).2
  calc
    I.val = A^2*squarefreePart I.val := by simpa only [hi] using (squarePart_sq_mul_squarefreePart I.val).symm
    _ = A^2*squarefreePart J.val := by rw [he]
    _ = J.val := by simpa only [hj] using squarePart_sq_mul_squarefreePart J.val

end CanonicalQuadraticSieve

end

end OAI
