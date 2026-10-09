import OAI.NumberTheory.DirichletL.QuadraticSieve.HighKernelGeometry
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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota
local notation "O" => ActualEisensteinCubic.O

instance complexSLTopology : TopologicalSpace (SL(2,ℂ)) :=
  inferInstanceAs (TopologicalSpace {A : Matrix (Fin 2) (Fin 2) ℂ // A.det=1})

lemma continuous_complexSL_coe :
    Continuous (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
  continuous_subtype_val

lemma continuous_complexSL_mul (g : SL(2,ℂ)) :
    Continuous (fun h : SL(2,ℂ) => g*h) := by
  apply Continuous.subtype_mk
  change Continuous (fun h : SL(2,ℂ) =>
    (g : Matrix (Fin 2) (Fin 2) ℂ)*(h : Matrix (Fin 2) (Fin 2) ℂ))
  exact continuous_const.mul continuous_complexSL_coe

lemma continuous_coordinateSection : Continuous coordinateSection := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hroot : Continuous (fun w : UpperCoordinates => (Real.sqrt w.1.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_snd.comp continuous_subtype_val))
  have hne : ∀w : UpperCoordinates,(Real.sqrt w.1.2 : ℂ)≠0 := fun w =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.2).ne'
  fin_cases i <;> fin_cases j
  · exact hroot
  · exact (continuous_fst.comp continuous_subtype_val).div hroot hne
  · exact continuous_const
  · exact hroot.inv₀ hne

lemma continuous_hyperbolicProjection :
    Continuous (fun g : SL(2,ℂ) => (g : HyperbolicSpace)) :=
  continuous_quotient_mk'

lemma continuous_upperCoordinates :
    Continuous (fun w : UpperCoordinates => upperPoint w.1.1 w.1.2 w.2) :=
  continuous_hyperbolicProjection.comp continuous_coordinateSection

lemma continuous_translatedUpperCoordinates (g : SL(2,ℂ)) :
    Continuous (fun w : UpperCoordinates => g • upperPoint w.1.1 w.1.2 w.2) := by
  exact continuous_hyperbolicProjection.comp
    ((continuous_complexSL_mul g).comp continuous_coordinateSection)

def integralOrbitRel (H : Subgroup (SL(2,O))) : Setoid HyperbolicSpace where
  r w w' := ∃h : H, integralComplexMatrix (h:SL(2,O)) • w = w'
  iseqv := ⟨by intro w; exact ⟨1,by simp⟩,
    by
      rintro w w' ⟨h,hh⟩
      refine ⟨h⁻¹,?_⟩
      rw [←hh]
      simp [←mul_smul],
    by
      rintro w w' w'' ⟨h,hh⟩ ⟨k,hk⟩
      refine ⟨k*h,?_⟩
      simpa only [Subgroup.coe_mul,map_mul,mul_smul,hh] using hk⟩

abbrev IntegralOrbitQuotient (H : Subgroup (SL(2,O))) := Quotient (integralOrbitRel H)

def integralOrbitProjection (H : Subgroup (SL(2,O))) :
    HyperbolicSpace → IntegralOrbitQuotient H := Quotient.mk _

lemma continuous_integralOrbitProjection (H : Subgroup (SL(2,O))) :
    Continuous (integralOrbitProjection H) := continuous_quotient_mk'

lemma integralOrbitProjection_eq (H : Subgroup (SL(2,O))) (h : H) (w : HyperbolicSpace) :
    integralOrbitProjection H (integralComplexMatrix (h:SL(2,O)) • w)=
      integralOrbitProjection H w := by
  apply Eq.symm
  exact Quotient.sound ⟨h,rfl⟩

end

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

def truncatedFordLift (T : ℝ) (p : truncatedFordBox T) : UpperCoordinates :=
  ⟨p.1,lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2/3)) p.2.2.1⟩

lemma continuous_truncatedFordLift (T : ℝ) : Continuous (truncatedFordLift T) :=
  continuous_subtype_val.subtype_mk _

def fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) (p : UpperCoordinates) :
    IntegralOrbitQuotient H := integralOrbitProjection H
      (integralComplexMatrix r⁻¹ • upperPoint p.1.1 p.1.2 p.2)

lemma continuous_fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) :
    Continuous (fordOrbitChart H r) :=
  (continuous_integralOrbitProjection H).comp
    (continuous_translatedUpperCoordinates (integralComplexMatrix r⁻¹))

def compactFordCore (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  ⋃r∈S, Set.range (fun p : truncatedFordBox T => fordOrbitChart H r (truncatedFordLift T p))

lemma compactFordCore_isCompact (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    IsCompact (compactFordCore H S T) := by
  let : CompactSpace (truncatedFordBox T) :=
    isCompact_iff_compactSpace.mp (truncatedFordBox_isCompact T)
  apply S.isCompact_biUnion
  intro r hr
  exact isCompact_range ((continuous_fordOrbitChart H r).comp (continuous_truncatedFordLift T))

def fordCuspTail (H : Subgroup (SL(2,O))) (r : SL(2,O)) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  fordOrbitChart H r '' {p : UpperCoordinates | Complex.normSq p.1.1≤1/3 ∧
    Real.sqrt (2/3)≤p.1.2 ∧ T<p.1.2}

theorem finiteIndex_compact_core_cusp_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore H S T) ∧
      Set.univ=compactFordCore H S T ∪ ⋃r∈S, fordCuspTail H r T := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  refine ⟨S,fun T => ⟨compactFordCore_isCompact H S T,?_⟩⟩
  apply Set.Subset.antisymm
  · intro q hq
    induction q using Quotient.inductionOn with | _ w =>
      obtain ⟨h,r,hr,z,v,hv,heq,hz,hfloor⟩ := hS w
      have hqeq : integralOrbitProjection H w=fordOrbitChart H r ⟨(z,v),hv⟩ := by
        rw [←integralOrbitProjection_eq H h w,heq]
        rfl
      change integralOrbitProjection H w∈_
      rw [hqeq]
      by_cases hT : v≤T
      · apply Or.inl
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),mem_truncatedFordBox z v T hz hfloor hT⟩,rfl⟩
      · apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),hv⟩,⟨hz,hfloor,lt_of_not_ge hT⟩,rfl⟩
  · exact Set.subset_univ _

theorem globalKubotaKernel_compact_core_cusp_cover :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore globalKubotaKernel S T) ∧
      Set.univ=compactFordCore globalKubotaKernel S T ∪ ⋃r∈S, fordCuspTail globalKubotaKernel r T := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_compact_core_cusp_cover globalKubotaKernel

end CubicEisenstein

namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (tupleSourceSum densityChildEnergy)
open JointLogSeparation (outerWindow)

local instance {ι : Type*} : Nonempty (GlobalSecondData ι) :=
  ⟨⟨⟨0,0,∅,∅⟩,∅,∅,∅,⟨∅,∅,∅,0⟩⟩⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondRecover (s : Finset (GlobalSecondData ι)) : SecondPassFiber.OldTuple → GlobalSecondData ι :=
  Function.invFunOn (globalSecondTuple p) s

theorem globalSecondRecover_apply
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (s : Finset (GlobalSecondData ι)) (q : Ideal O × Ideal O × Ideal O)
    (hs : ∀ x∈s,GlobalSecondAdmissible x) (hq : ∀ x∈s,globalSecondFixedTriple p x=q)
    (x : GlobalSecondData ι) (hx : x∈s) :
    globalSecondRecover p s (globalSecondTuple p x)=x := by
  have hi : Set.InjOn (globalSecondTuple p) s := by
    intro x hx y hy h
    exact globalSecondEncoding_injective p hinj (hs x hx) (hs y hy) ((hq x hx).trans (hq y hy).symm) h
  exact hi.leftInvOn_invFunOn hx

def globalSecondSource (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ,ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x∈s,w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x)) A₁ A₂ W V
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem globalSecondSource_eq_tupleSource
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (s : Finset (GlobalSecondData ι)) (q : Ideal O × Ideal O × Ideal O)
    (hs : ∀ x∈s,GlobalSecondAdmissible x) (hq : ∀ x∈s,globalSecondFixedTriple p x=q)
    (w : GlobalSecondData ι → ℂ) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) :
    globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    tupleSourceSum p hp hcop hg (s.image (globalSecondTuple p))
      (w ∘ globalSecondRecover p s) (globalSecondLabel p ∘ globalSecondRecover p s)
      F Ψ₁ Ψ₂ m A₁ A₂ W V (z ∘ globalSecondRecover p s) (ud ∘ globalSecondRecover p s)
      (ue ∘ globalSecondRecover p s) (uv ∘ globalSecondRecover p s) (kap ∘ globalSecondRecover p s) X₁ X₂ R := by
  unfold globalSecondSource tupleSourceSum
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    simp only [Function.comp_apply,globalSecondRecover_apply p hinj s q hs hq x hx]
  · intro x hx y hy he
    exact globalSecondEncoding_injective p hinj (hs x hx) (hs y hy) ((hq x hx).trans (hq y hy).symm) he

end

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label)
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (outerWindow)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondRawPool (F : Finset ι) (x : GlobalSecondData ι) : Finset ι :=
  (F\(x.cube.support∪x.common))\x.firstCommon

def globalSecondRawMask (m : O) (x : GlobalSecondData ι) : O :=
  m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit *
    primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)

def globalSecondRawSource (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ,ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x∈s,w x * postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x) Ψ₁ Ψ₂
    (globalSecondRawMask p m x) (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x)) A₁ A₂ W V
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem globalSecondRawSource_eq
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (q : Ideal O × Ideal O × Ideal O) (hfixed : ∀ x∈s,globalSecondFixedTriple p x=q)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) (hR : 0 < R) :
    globalSecondRawSource p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ (fixedTripleMask m q)
      A₁ A₂ W V z ud ue uv kap X₁ X₂ R := by
  obtain ⟨C,hC,hsep⟩ := postCommonSmoothPair_uniform_fixed_tests p hp hcop hg A₁ A₂ W V M hM hV 0 0
  obtain ⟨b,hb,hid⟩ := hsep R hR
  unfold globalSecondRawSource globalSecondSource
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg (fun a : ℂ => w x * a)
  rw [hid (globalSecondRawPool F x) Ψ₁ Ψ₂ (globalSecondRawMask p m x) (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂,
    hid F Ψ₁ Ψ₂ (fixedTripleMask m q) (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂]
  simp only [separatedPostCommon,globalSecondRawPool,globalSecondRawMask,
    globalSecondRawRow_fixed_pool p hp hcop hg hinj,hfixed x hx]

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct jLabel b0Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

namespace CubeCoordinates
def sideDivisor {ι : Type*} (x : CubeCoordinates ι) (side : Bool) : Finset ι :=
  if side then x.leftDivisor else x.rightDivisor
end CubeCoordinates

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalCubeJNorm (x : GlobalSecondData ι) : ℝ :=
  ‖eisEmbedding (jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit)‖^2

def globalCubeActiveRoot (x : GlobalSecondData ι) : ℝ :=
  ‖eisEmbedding (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖

def globalFirstColumnScale (ell : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  ell/(primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common)

def globalFirstRowScale (K ell B F : ℝ) (x : GlobalSecondData ι) : ℝ :=
  ell^2*B^4*F^2*primeProductNorm p x.firstDivisor/
    (K*(primeProductNorm p x.common)^2*globalCubeJNorm p x)

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeActiveRoot_pos (x : GlobalSecondData ι) : 0 < globalCubeActiveRoot p x := by
  have hh := element_norm_ge_one (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)
    (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  change 0 < ‖eisEmbedding _‖
  nlinarith [norm_nonneg (eisEmbedding (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i))]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstColumnScale_pos (ell : ℝ) (hell : 0 < ell) (x : GlobalSecondData ι) (side : Bool) :
    0 < globalFirstColumnScale p ell x side :=
  div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalBaseLabel_norm (x : GlobalSecondData ι) :
    ‖eisEmbedding (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
      x.cube.leftBit x.cube.rightBit)‖^2 = primeProductNorm p x.common*globalCubeJNorm p x := by
  simp only [secondBaseLabel,map_mul,norm_mul,mul_pow,primeSubsetGenerator_norm_eq_productNorm,globalCubeJNorm]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

section

end

end SecondPassArithmetic

end

end OAI
