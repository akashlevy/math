import OAI.NumberTheory.DirichletL.GaussSum.ResidualEquivalence
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

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)
variable (Q:Ideal Eis) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})))

abbrev activeStratum :=
  freePrimaryControlledStratum D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported c hcQ h G A

def sourceRowScalar (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ) : ℂ := by
  letI : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  exact fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
    G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)*
    (D.activeStratum Q c hcQ h G A).modelRowPhase G.shape
      (fun P=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val)
      (fun P=>freePrimaryPrime_good D.movingIdeal _ D.movingSupported P.val)
      (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6) u n

lemma sourceRowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (u:Eisˣ) (n:ℕ) :
    ‖D.sourceRowScalar Q c hc hcQ h G A Ψ u n‖≤1 := by
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  have hp:(G.c0*∏P:A,freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)≠0:=
    mul_ne_zero G.denominator_ne_zero (Finset.prod_ne_zero_iff.mpr
      (fun P _=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val))
  have hs:=G.shape.stratumShapeFactor_norm _ hp
  have hr:=(D.activeStratum Q c hcQ h G A).modelRowPhase_norm
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ
      (fun P:A=>freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)
      (fun P _=>freePrimaryPrime_primary D.movingIdeal _ D.movingSupported P.val))
    G.primary G.shape
    (fun P=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val)
    (fun P=>freePrimaryPrime_good D.movingIdeal _ D.movingSupported P.val)
    (fun P=>freePrimaryPrime_odd D.movingIdeal _ D.movingSupported P.val)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6)
    (fun _=>Nat.mod_lt _ (by decide)) u n
  unfold sourceRowScalar
  rw [norm_mul,norm_mul,hs,hr,mul_one,mul_one]
  exact D.fixedCoefficient_norm Ψ Q hΨ c hc h

def sourceRowResidue : G.PhaseResidue :=
  Ideal.Quotient.mk _ (-((D.activeStratum Q c hcQ h G A).matrix (fun _=>1) 1 1)*
    (D.activeStratum Q c hcQ h G A).U)

def selectedSourceRowScalar (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ)
    (rho:G.PhaseResidue) (k dN dB:Ideal Eis) : ℂ :=
  if rho=D.sourceRowResidue Q c hcQ h G A then
    D.sourceRowScalar Q c hc hcQ h G A Ψ u n*residualArgumentPhase k 1 dN dB else 0

lemma selectedSourceRowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (u:Eisˣ) (n:ℕ)
    (rho:G.PhaseResidue) (k dN dB:Ideal Eis) :
    ‖D.selectedSourceRowScalar Q c hc hcQ h G A Ψ u n rho k dN dB‖≤1 := by
  unfold selectedSourceRowScalar
  split_ifs
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (D.sourceRowScalar_norm Q c hc hcQ h G A Ψ hΨ u n)).trans (residualArgumentPhase_norm_le_one k 1 dN dB)
  · simp

end GoodMaskRowData
end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

theorem completedT_eq_actualControlledSource
    (Q:Ideal Eis) (hQ:Q≠0) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (Ψ:Eis→*ℂ) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ m f z) W X=
      actualControlledSource D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported
        c hc hcQ G (D.fixedFactor Ψ Q) W X := by
  rw [D.completedT_eq_fixedFactor Ψ Q hmLam hm2 W X]
  apply fixedFree_completedT_eq_actualControlledSource D.movingIdeal _ D.movingSupported _
    c hc hcQ G (D.fixedFactor Ψ Q) (D.fixedFactor_periodic Ψ Q hΨ)
    (D.fixedFactor_norm Ψ Q hΨnorm) W lo hi hlo hsupp hW X hX
  apply mul_ne_zero hQ
  apply Ideal.span_singleton_eq_bot.not.mpr
  norm_num

end GoodMaskRowData
end

variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def residualActivePrimes (e:α⊕β ≃ γ) : Finset γ :=
  Finset.univ.image (fun a:α=>e (Sum.inl a))

omit [Fintype β] [Fintype γ] in
lemma residualActivePrimes_not_inr (e:α⊕β ≃ γ) (b:β) :
    e (Sum.inr b)∉residualActivePrimes e := by
  intro h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h
  cases e.injective ha

def nonresidualComplementMap (e:α⊕β ≃ γ) : β → {g:γ // g∉residualActivePrimes e} :=
  fun b=>⟨e (Sum.inr b),residualActivePrimes_not_inr e b⟩

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementMap_bijective (e:α⊕β ≃ γ) :
    Function.Bijective (nonresidualComplementMap e) := by
  constructor
  · intro a b hab
    exact Sum.inr.inj (e.injective (congrArg Subtype.val hab))
  · intro g
    obtain ⟨x,hx⟩:=e.surjective g.val
    cases x with
    | inl a=>
      exact (g.property (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,hx⟩)).elim
    | inr b=>exact ⟨b,Subtype.ext hx⟩

noncomputable def nonresidualComplementEquiv (e:α⊕β ≃ γ) :
    β ≃ {g:γ // g∉residualActivePrimes e} :=
  Equiv.ofBijective (nonresidualComplementMap e) (nonresidualComplementMap_bijective e)

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementEquiv_val (e:α⊕β ≃ γ) (b:β) :
    (nonresidualComplementEquiv e b).val=e (Sum.inr b) := rfl

omit [Fintype β] [Fintype γ] in
lemma complementActive_image (e:α⊕β ≃ γ) (B:Finset β) :
    (B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val=
      B.image (fun b=>e (Sum.inr b)) := by
  simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
    Equiv.toEmbedding_apply,nonresidualComplementEquiv_val]

lemma inactive_product_nonresidual (e:α⊕β ≃ γ) (z:γ → ℂ) (B:Finset β) :
    (∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
      B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)=
      ∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)) := by
  symm
  apply Finset.prod_equiv (nonresidualComplementEquiv e)
  · intro b
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_map_equiv,
      Equiv.symm_apply_apply]
  · intro b hb
    rfl

theorem inactive_weight_nonresidual_subsets (e:α⊕β ≃ γ) (z:γ → ℂ)
    (hz:∀a:α,z (e (Sum.inl a))=0) (F:Finset γ → ℂ) :
    (∑A:Finset γ,(∏g∈(Finset.univ:Finset γ)\A,z g)*F A)=
      ∑B:Finset β,(∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)))*
        F (residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))) := by
  have hres:∀g∈residualActivePrimes e,z g=0:=by
    intro g hg
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hg
    exact hz a
  rw [CompletedGauss.inactive_weight_optional_active (residualActivePrimes e) z hres F]
  symm
  apply Fintype.sum_equiv (nonresidualComplementEquiv e).finsetCongr
  intro B
  change _=(∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
    B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)*
    F (residualActivePrimes e∪(B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val)
  rw [inactive_product_nonresidual,complementActive_image]

end CanonicalRowCompletion

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma actual_bracket_ideal_congr (P Q:Ideal Eis) [P.IsMaximal] [Q.IsMaximal]
    (hP:lambda∉P) (hQ:lambda∉Q) (hPQ:P=Q) (j:ℕ) (z:Eis) :
    bracket (actualSextic P hP) j (Ideal.Quotient.mk P z)=
      bracket (actualSextic Q hQ) j (Ideal.Quotient.mk Q z) := by
  subst Q
  rfl

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve
namespace FixedFourierGeometry

end FixedFourierGeometry
end CubicEisenstein

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass
open ConcretePrimeRowBridge SecondPassArithmetic
local notation "Eis" => ActualEisensteinCubic.O

def HasFixedShellModels (S:Finset (Ideal Eis)) (base:Eis→*ℂ)
    (rays:ℕ) (scale:ℂ) (ρ q level:ℝ) : Prop :=
  ∀ Ψ:Eis→*ℂ,IsBaseRayTwist base Ψ→∀m:Eis,m≠0→
    ∀ F:ℝ,∀f:idealRange F,∀u:Eisˣ,∀ W:ℝ→ℂ,∀a b:ℝ,
      0<a→Function.support W⊆Set.Icc a b→ContDiff ℝ ∞ W→
      ∀K X:ℝ,0<K→0<X→∀rows:Finset (Ideal Eis),
        (∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)→
        HasExactCompletedModels rays rows K X ρ q level f.val
          (Ideal.span {m*excludedGenerator S}*f.val) W
          (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) scale

lemma normTwistedSource_contDiff (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (t:ℝ) :
    ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W t) := by
  have he:(CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t:ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t:=by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  rw [←he]
  exact (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t).smooth ⊤

theorem hasCanonicalThetaModels_of_fixed_shell_models
    (S:Finset (Ideal Eis)) (base:Eis→*ℂ) (rays:ℕ) (scale:ℂ) (ρ q level:ℝ)
    (hmodels:HasFixedShellModels S base rays scale ρ q level) :
    HasCanonicalThetaModels S base ρ q level := by
  intro A hA W hs hW κ hκ
  refine ⟨(rays:ℝ)^2*‖scale‖^2,by positivity,?_⟩
  intro Z K X F θ hZ hK hX hF hFZ Ψ hΨ m hm
  dsimp only
  intro hmargin
  refine ⟨rays,scale,?_,?_⟩
  · exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hκ.le)
  · intro u f H hH
    have hH0:H≠0:=((mem_shortCubeRange _ H).mp hH).1
    have hHN:(0:ℝ)<(Ideal.absNorm H:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hH0)
    have hXH:0<X/(Ideal.absNorm H:ℝ)^3:=by positivity
    have hsTw:Function.support (CompletedHeight.normTwistedSource W θ)⊆
        Set.Icc (Real.exp (-A)) (Real.exp A):=
      (CompletedHeight.normTwistedSource_support W θ).trans hs
    have hTw:=normTwistedSource_contDiff W (Real.exp (-A)) (Real.exp A)
      (Real.exp_pos _) hs hW θ
    let rows:=((firstFrequencyDisk (2*K)).erase 0).image (fun z:Eis=>Ideal.span {z})
    have hrows:∀I∈rows,I≠0:=by
      intro I hI
      obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
      exact Ideal.span_singleton_eq_bot.not.mpr (Finset.mem_erase.mp hz).1
    intro j hj
    exact hmodels Ψ hΨ m hm F f u (CompletedHeight.normTwistedSource W θ)
      (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) hsTw hTw
      ((2:ℝ)^j) (X/(Ideal.absNorm H:ℝ)^3) (by positivity) hXH
      (completedRowDyad rows j) (completedRowDyad_bounds rows j hrows)

end CanonicalRowCompletion

namespace CompletedGauss.ReflectedBranchData
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
variable {levelBound K:ℝ} {I F Q:Ideal Eis}
variable (d:ReflectedBranchData levelBound K I F Q)
variable (η:ℕ→Ideal Eis→Ideal Eis→ℂ)
variable (σ τ:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
variable (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q))

lemma rawValue_congr_phase_at (h:∀m,σ m k=τ m k) :
    d.rawValue η σ W X ρ q k=d.rawValue η τ W X ρ q k := by
  unfold rawValue
  apply tsum_congr
  intro x
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,h]

lemma rawValue_zero_phase : d.rawValue η (fun _ _=>0) W X ρ q k=0 := by
  unfold rawValue
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,zero_mul,tsum_zero]

lemma rawValue_mul_phase_at (a:idealRange (completedResidualScale K I Q)→ℂ) :
    d.rawValue η (fun m l=>a l*σ m l) W X ρ q k=a k*d.rawValue η σ W X ρ q k := by
  unfold rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  unfold rawDualKernelTerm canonicalRawBranchCoefficient
  ring

end CompletedGauss.ReflectedBranchData

namespace CanonicalRowCompletion
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) : Finset γ :=
  residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))

omit [Fintype β] [Fintype γ] in
lemma completeActiveSet_residual (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    e (Sum.inl a)∈completeActiveSet e B :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)

omit [Fintype γ] in
lemma optionalPrimeActive_completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) :
    optionalPrimeActive e (completeActiveSet e B)=B := by
  ext b
  rw [mem_optionalPrimeActive]
  change e (Sum.inr b)∈residualActivePrimes e∪B.image (fun b=>e (Sum.inr b)) ↔ b∈B
  simp only [Finset.mem_union,residualActivePrimes_not_inr,false_or,Finset.mem_image]
  constructor
  · rintro ⟨b',hb',he⟩
    have hb:b'=b:=Sum.inr.inj (e.injective he)
    exact hb ▸ hb'
  · intro hb
    exact ⟨b,hb,rfl⟩

noncomputable def selectedActiveEquiv (e:α⊕β ≃ γ) (B:Finset β) :
    α⊕B ≃ completeActiveSet e B := by
  let t : B ≃ optionalPrimeActive e (completeActiveSet e B):={
    toFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    invFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (Equiv.sumCongr (Equiv.refl _) t).trans
    (activePrimeUnionEquiv e (completeActiveSet e B) (completeActiveSet_residual e B))

omit [Fintype γ] in
lemma selectedActiveEquiv_inl (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    (selectedActiveEquiv e B (Sum.inl a)).val=e (Sum.inl a) := rfl

omit [Fintype γ] in
lemma selectedActiveEquiv_inr (e:α⊕β ≃ γ) (B:Finset β) (b:B) :
    (selectedActiveEquiv e B (Sum.inr b)).val=e (Sum.inr b.val) := rfl

end CanonicalRowCompletion

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def maskElement (q:ℕ) (m:Eis) : Eis := m*excludedGenerator (reflectionExcludedPrimes q)
def maskIdeal (q:ℕ) (m:Eis) (F:Ideal Eis) : Ideal Eis := Ideal.span {maskElement q m}*F
def freeConductor (q:ℕ) : Ideal Eis := CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}
abbrev RowIndex (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis)) (R F:Ideal Eis) :=
  representativeRowFiber rows R (maskIdeal q m F)

lemma maskElement_ne_zero (q:ℕ) (m:Eis) (hm:m≠0) : maskElement q m≠0 :=
  mul_ne_zero hm (reflectionExcludedGenerator_ne_zero q)
lemma maskIdeal_ne_zero (q:ℕ) (m:Eis) (hm:m≠0) (F:Ideal Eis) (hF:F≠0) : maskIdeal q m F≠0 :=
  mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (maskElement_ne_zero q m hm)) hF
lemma mask_bad (q:ℕ) (m:Eis) (F:Ideal Eis) : ∀P∈fixedBadPrimes,P∣maskIdeal q m F :=
  reflection_row_mask_bad q m F

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)

noncomputable def data (J:RowIndex q m rows R F) :
    GoodMaskRowData (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val) :=
  fiberGoodMaskRowData rows R F (maskElement q m) (maskElement_ne_zero q m hm) hF.ne_zero hrows v J

noncomputable def splitIndex (J:RowIndex q m rows R F) :
    PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.pool R (maskIdeal q m F) (freeConductor q) ≃
      FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) := by
  have hJ:J.val≠0:=hrows J.val (Finset.mem_filter.mp J.property).1
  have hz:Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator J.val}=J.val:=by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
  have parts:=representativeFiber_parts rows R (maskIdeal q m F) J
  exact (data q m hm rows R F hF hrows v J).primeFiberEquiv R J.val F (freeConductor q)
    hR hJ hF (maskElement_ne_zero q m hm) (ConcretePrimeRowBridge.span_idealGenerator F) hz
    (mask_bad q m F) (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm

noncomputable def activeSet (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F) :
    Finset (FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q)) :=
  completeActiveSet (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e)

def columnDivisor (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (side:Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor
    (fun P:FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e=>P.val)
    (fun P=>completedLocalExponent R F P.val)
    (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e) side

variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

noncomputable def rowScalar (Ψ:Eis→*ℂ)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) : ℂ :=
  (data q m hm rows R F hF hrows v J).selectedSourceRowScalar
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) Ψ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)

lemma rowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) :
    ‖rowScalar q hq m hm rows R F hR hF hrows v Ψ x n J‖≤1 := by
  exact (data q m hm rows R F hF hrows v J).selectedSourceRowScalar_norm
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) Ψ hΨ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)

noncomputable def reflectedFiber (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      (fixedCuspLevelBound (reflectionConductor q)) K R F (maskIdeal q m F) :=
  FreeReflection.fixedRayFiberFromRows (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    rows R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun a J=>rowScalar q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J)
    (fun a J=>rowScalar_norm q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J)

end CanonicalRowCompletion.ActualFiber

end

end OAI
