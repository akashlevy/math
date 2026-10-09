import OAI.NumberTheory.DirichletL.GaussSum.ReflectedBranches
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

open scoped Manifold ENNReal MatrixGroups

namespace CubicEisenstein

def kernelTestPartial (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) : ℂ :=
  fderiv ℝ (kernelTestField f) (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)

lemma kernelTestPartial_add (f g : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (f+g) w j=kernelTestPartial f w j+kernelTestPartial g w j := by
  unfold kernelTestPartial
  have he : kernelTestField (f+g)=kernelTestField f+kernelTestField g := rfl
  rw [he,fderiv_add ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))
    ((kernelTestField_contDiffAt g _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestPartial_smul (c : ℂ) (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (c•f) w j=c*kernelTestPartial f w j := by
  unfold kernelTestPartial
  have he : kernelTestField (c•f)=c•kernelTestField f := rfl
  rw [he,fderiv_const_smul ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestEnergyDensity_eq_partials (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f w=(hyperbolicHeight w)^2*∑j:Fin 3,‖kernelTestPartial f w j‖^2 := by
  have hd := ((kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)).hasFDerivAt
  have hr := (Complex.reCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  change fderiv ℝ (fun p => (kernelTestField f p).re) (hyperbolicEuclideanCoordinates w)=_ at hr
  change fderiv ℝ (fun p => (kernelTestField f p).im) (hyperbolicEuclideanCoordinates w)=_ at hi
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  rw [hr,hi,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change (kernelTestPartial f w j).re^2+(kernelTestPartial f w j).im^2=‖kernelTestPartial f w j‖^2
  simpa only [Complex.normSq_apply,pow_two] using Complex.normSq_eq_norm_sq (kernelTestPartial f w j)

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups InnerProductSpace

def kernelGradientAt (w : HyperbolicSpace) : kernelSmoothTests→ₗ[ℂ]EuclideanSpace ℂ (Fin 3) where
  toFun f := WithLp.toLp 2 (fun j => (hyperbolicHeight w:ℂ)*kernelTestPartial f w j)
  map_add' f g := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_add,mul_add]
  map_smul' c f := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_smul,smul_eq_mul,mul_left_comm]

lemma kernelGradientAt_norm_sq (w : HyperbolicSpace) (f : kernelSmoothTests) :
    ‖kernelGradientAt w f‖^2=kernelTestEnergyDensity f w := by
  rw [PiLp.norm_sq_eq_of_L2,kernelTestEnergyDensity_eq_partials]
  change (∑j:Fin 3,‖(hyperbolicHeight w:ℂ)*kernelTestPartial f w j‖^2)=_
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (hyperbolicHeight_pos w).le,
    Finset.mul_sum]

def kernelDirichletPairDensity (f g : kernelSmoothTests) (q : KernelQuotient) : ℂ :=
  ((kernelQuotientEnergyDensity (f+g) q:ℂ)-(kernelQuotientEnergyDensity (f-g) q:ℂ)+
    ((kernelQuotientEnergyDensity (f-Complex.I•g) q:ℂ)-
      (kernelQuotientEnergyDensity (f+Complex.I•g) q:ℂ))*Complex.I)/4

lemma kernelDirichletPairDensity_coordinate (f g : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)=
      inner ℂ (kernelGradientAt w f) (kernelGradientAt w g) := by
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [←map_add,←map_sub,←map_smul,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
  rfl

lemma kernelDirichletPairDensity_integrable (f g : kernelSmoothTests) :
    Integrable (kernelDirichletPairDensity f g) (integralQuotientVolume globalKubotaKernel) := by
  have hf : ∀h : kernelSmoothTests,Integrable (fun q => (kernelQuotientEnergyDensity h q:ℂ))
      (integralQuotientVolume globalKubotaKernel) := fun h =>
    (kernelQuotientEnergyDensity_integrable h).ofReal
  exact ((hf (f+g)).sub (hf (f-g)) |>.add (((hf (f-Complex.I•g)).sub (hf (f+Complex.I•g))).mul_const _)).div_const _

lemma kernelDirichletPairDensity_add_right (f g h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (g+h) q=kernelDirichletPairDensity f g q+kernelDirichletPairDensity f h q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_add,inner_add_right]

lemma kernelDirichletPairDensity_smul_right (c : ℂ) (f g : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (c•g) q=c*kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_smul,inner_smul_right]

lemma kernelDirichletPairDensity_conj (f g : kernelSmoothTests) (q : KernelQuotient) :
    star (kernelDirichletPairDensity g f q)=kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change star (kernelDirichletPairDensity g f (integralOrbitProjection globalKubotaKernel w))=
      kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)
    rw [kernelDirichletPairDensity_coordinate,kernelDirichletPairDensity_coordinate]
    exact inner_conj_symm _ _

lemma kernelDirichletPairDensity_self (f : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f f q=(kernelQuotientEnergyDensity f q:ℂ) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f f (integralOrbitProjection globalKubotaKernel w)=_
    rw [kernelDirichletPairDensity_coordinate,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
    rfl

def kernelDirichletForm (f g : kernelSmoothTests) : ℂ :=
  ∫q,kernelDirichletPairDensity f g q ∂integralQuotientVolume globalKubotaKernel

lemma kernelDirichletForm_add_right (f g h : kernelSmoothTests) :
    kernelDirichletForm f (g+h)=kernelDirichletForm f g+kernelDirichletForm f h := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_add_right]
  exact integral_add (kernelDirichletPairDensity_integrable f g) (kernelDirichletPairDensity_integrable f h)

lemma kernelDirichletForm_smul_right (c : ℂ) (f g : kernelSmoothTests) :
    kernelDirichletForm f (c•g)=c*kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_smul_right]
  exact integral_const_mul _ _

lemma kernelDirichletForm_conj (f g : kernelSmoothTests) :
    star (kernelDirichletForm g f)=kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp only [Complex.star_def]
  rw [←integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (kernelDirichletPairDensity_conj f g)

lemma kernelDirichletForm_self (f : kernelSmoothTests) :
    kernelDirichletForm f f=(kernelDirichletEnergy f:ℂ) := by
  unfold kernelDirichletForm kernelDirichletEnergy
  simp_rw [kernelDirichletPairDensity_self]
  exact integral_complex_ofReal

end CubicEisenstein

namespace CompletedGauss

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory

theorem finite_integral_energy_bound {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (E : ℝ) (hE : 0≤E)
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀k,Integrable (fun t => b t*φ k t))
    (hbound : ∀t,(∑k,‖φ k t‖^2)≤E) :
    (∑k,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,‖b t‖)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ→EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖≤‖b t‖*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE]
    change (∑k,‖b t*φ k t‖^2)≤‖b t‖^2*E
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫t : ℝ,F t)=e.symm (fun k => ∫t : ℝ,b t*φ k t) := by
    rw [show F=(fun t => e.symm (fun k => b t*φ k t)) from rfl,e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫t : ℝ,b t*φ k t)‖≤(∫t : ℝ,‖b t‖)*Real.sqrt E := by
    rw [←he,←integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

open CanonicalQuadraticSieve ActualEisensteinCubic

theorem integrated_product_quadratic (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : ℝ→Ideal O→Ideal O→ℂ,
      (∀n b,Continuous (fun t => β t n b)) →
      (∀t,∀n∈S,∀b∈T,‖β t n b‖≤lengthScale) →
    ∀rowPhase : idealRange K→ℝ→ℂ,(∀k,Continuous (rowPhase k)) → (∀k t,‖rowPhase k t‖≤1) →
    ∀b : 𝓢(ℝ,ℂ),
      (∑k : idealRange K,‖∫t : ℝ,b t*(rowPhase k t*
        ∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β t n v)‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2*(∫t : ℝ,‖b t‖)^2 := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_scaled ε hε
  refine ⟨C,hC,?_⟩
  intro K U B lengthScale hK hU hB hL S T hS hT β hβc hβ rowPhase hωc hω b
  let E := C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2
  have hE : 0≤E := by dsimp [E]; positivity
  let φ : idealRange K→ℝ→ℂ := fun k t => rowPhase k t*
    ∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β t n v
  have hφc (k : idealRange K) : Continuous (φ k) := by
    apply (hωc k).mul
    apply continuous_finsetSum
    intro n hn
    apply continuous_finsetSum
    intro v hv
    exact continuous_const.mul (hβc n v)
  have hφbound (t : ℝ) : (∑k,‖φ k t‖^2)≤E := by
    apply le_trans _ (hbound K U B lengthScale hK hU hB hL S T hS hT (β t) (hβ t))
    apply Finset.sum_le_sum
    intro k hk
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω k t)) 2
  have hpoint (k : idealRange K) (t : ℝ) : ‖φ k t‖≤Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖φ j t‖) (Finset.mem_univ k)).trans (hφbound t)
  have hφint (k : idealRange K) : Integrable (fun t : ℝ => b t*φ k t) :=
    b.integrable.mul_bdd (hφc k).aestronglyMeasurable (Filter.Eventually.of_forall (hpoint k))
  exact finite_integral_energy_bound b φ E hE b.integrable.norm hφint hφbound

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve

def completedRowFiber (S : Finset (Ideal O)) (Q A T : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => rowPowerfulPart I=A ∧ rowMaskPart I Q=T)

theorem rowResidualPart_injective_on_fiber (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hS : ∀I∈S,I≠0) : Set.InjOn (fun I => rowResidualPart I Q) (completedRowFiber S Q A T) := by
  intro I hI J hJ he
  change rowResidualPart I Q=rowResidualPart J Q at he
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
  calc
    I = rowPowerfulPart I*rowMaskPart I Q*rowResidualPart I Q := (row_powerful_mask_residual_product I Q (hS I hIS)).symm
    _ = rowPowerfulPart J*rowMaskPart J Q*rowResidualPart J Q := by rw [hIA,hJA,hIT,hJT,he]
    _ = J := row_powerful_mask_residual_product J Q (hS J hJS)

theorem completedRowFiber_residual_range (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (I : Ideal O)
    (hI : I∈completedRowFiber S Q A T) :
    rowResidualPart I Q∈idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))) := by
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  apply mem_idealRange.mpr
  refine ⟨rowResidualPart_admissible I Q hbad,?_⟩
  rw [rowResidualPart_norm I Q (hS I hIS).1,hIA,hIT]
  exact div_le_div_of_nonneg_right (hS I hIS).2 (by positivity)

theorem completedRowFiber_energy_le (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (f : Ideal O→ℂ) :
    (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)≤
      ∑J : idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))),‖f J.val‖^2 := by
  let U := (completedRowFiber S Q A T).image (fun I => rowResidualPart I Q)
  have he : (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)=∑J∈U,‖f J‖^2 := by
    rw [Finset.sum_image (rowResidualPart_injective_on_fiber S Q A T (fun I hI => (hS I hI).1))]
  rw [he,Finset.sum_coe_sort (s := idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ)))) (f := fun J : Ideal O => ‖f J‖^2)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact completedRowFiber_residual_range S Q A T hbad K hS I hI
  · intro _ _ _
    exact sq_nonneg _

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

namespace InitialMeanSquare
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

def initialLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  ((CubicReflectionKernel.logProfile_compact W a b ha hs).mul_left
    (f := fun t : ℝ => (Real.exp (t/2) : ℂ))).toSchwartzMap (by
      change ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (t/2) : ℂ)*W (Real.exp t))
      have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (t/2)) :=
        Real.contDiff_exp.comp (contDiff_id.div_const 2)
      exact (Complex.ofRealCLM.contDiff.comp he).mul
        (hW.comp Real.contDiff_exp))

@[simp] lemma initialLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    initialLogProfile W a b ha hs hW t =
      (Real.exp (t/2) : ℂ)*W (Real.exp t) := rfl

theorem initialLogProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∀ t, initialLogProfile W a b ha hs hW t ≠ 0 →
      |t| ≤ |Real.log a|+|Real.log b|+1 := by
  intro t ht
  have hw : W (Real.exp t) ≠ 0 := by
    intro hz
    simp only [initialLogProfile_apply, hz, mul_zero] at ht
    exact ht rfl
  have hm := hs hw
  have hlo : Real.log a ≤ t := by
    simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  have hhi : t ≤ Real.log b := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos t) hm.2
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem initialLogProfile_normalized {ι : Type*} (p : ι → O)
    (hp : ∀ i, p i ≠ 0) (S : Finset ι) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) S =
      (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p S/Z) := by
  let n := ‖eisEmbedding (∏ i ∈ S,p i)‖
  have hn : 0 < n := norm_pos_iff.mpr
    (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
  have hpos : 0 < n^2/Z := div_pos (sq_pos_of_pos hn) hZ
  have hexp : Real.exp (Real.log (n^2/Z)/2)=n/Real.sqrt Z := by
    rw [←JointLogSeparation.sqrt_exp_half, Real.exp_log hpos,
      Real.sqrt_div (sq_nonneg n), Real.sqrt_sq hn.le]
  change ((Real.exp (Real.log (n^2/Z)/2) : ℂ)*W (Real.exp (Real.log (n^2/Z)))) /
    (n : ℂ) = (Real.sqrt Z : ℂ)⁻¹*W (n^2/Z)
  rw [hexp, Real.exp_log hpos, Complex.ofReal_div]
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hsz : (Real.sqrt Z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hZ).ne'
  field_simp

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma mobiusRow_mul (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (c : ℂ) (z : O) :
    mobiusRow p hg F Ψ m (fun S => c*H S) z = c*mobiusRow p hg F Ψ m H z := by
  simp only [mobiusRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [inputColumn]
  ring

omit [DecidableEq ι] in
theorem mobiusRow_initial_normalization (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z =
      (Real.sqrt Z : ℂ)⁻¹*mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z := by
  have hc : normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) =
      fun T => (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p T/Z) := by
    funext T
    exact initialLogProfile_normalized p hp T Z hZ W a b ha hs hW
  rw [hc, mobiusRow_mul]

omit [DecidableEq ι] in
theorem mobiusRow_initial_energy (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ‖mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z‖^2 =
      ‖mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z‖^2/Z := by
  rw [mobiusRow_initial_normalization p hg hp F Ψ m z Z hZ W a b ha hs hW,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hZ), mul_pow, inv_pow, Real.sq_sqrt hZ.le]
  ring

end InitialMeanSquare

end

end OAI
