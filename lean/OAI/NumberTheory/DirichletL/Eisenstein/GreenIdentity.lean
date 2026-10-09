import OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals
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
open scoped BigOperators Classical Topology

end CubicEisenstein

namespace CanonicalQuadraticSieve

theorem symmetric_truncation_scales (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    0 < X ∧ 0 < X₀/T ∧ X₀/T ≤ X ∧ X ≤ T*X₀ ∧ 0 ≤ T^4 := by
  have hT0 : 0 < T := by linarith
  have hX : 0 < X := by linarith
  refine ⟨hX,div_pos hX₀ hT0,?_,?_,by positivity⟩
  · apply (div_le_iff₀ hT0).mpr
    nlinarith
  · nlinarith

theorem symmetric_truncation_scalar_bound (m : ℕ) (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    ((X₀/T)/X)^(m+3) + 1/(1+(T*X₀)/X)^(m+3) +
      (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤
      (2 : ℝ)^(m+10)/T^m := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 < X := by linarith
  have hY : 0 < X₀/T := div_pos hX₀ hT0
  have hratio : (X₀/T)/X ≤ 2/T := by
    apply (div_le_iff₀ hX).mpr
    calc
      X₀/T ≤ (2*X)/T := div_le_div_of_nonneg_right (by linarith) hT0.le
      _ = (2/T)*X := by ring
  have hinv : 1/(1+(T*X₀)/X) ≤ 2/T := by
    have hz : T/2 ≤ (T*X₀)/X := (le_div_iff₀ hX).mpr (by nlinarith)
    calc
      _ ≤ 1/(T/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = 2/T := by field_simp
  have hpow : (2/T)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hT0 m)
      (pow_le_pow_right₀ hT1 (by omega : m ≤ m+3))
  have h₁ : ((X₀/T)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m :=
    (pow_le_pow_left₀ (by positivity) hratio _).trans hpow
  have h₂ : 1/(1+(T*X₀)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    simpa only [div_pow,one_pow] using (pow_le_pow_left₀ (by positivity) hinv (m+3)).trans hpow
  have hnum : X/(X₀/T) ≤ 2*T := by
    apply (div_le_iff₀ hY).mpr
    have he : 2*T*(X₀/T) = 2*X₀ := by field_simp
    rw [he]
    exact hhi
  have hmin : 1/(2*T) ≤ min 1 (X/(T*X₀)) := by
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
      linarith
    · apply (le_div_iff₀ (mul_pos hT0 hX₀)).mpr
      have he : 1/(2*T)*(T*X₀)=X₀/2 := by field_simp
      rwa [he]
  have hfreq : T ≤ 1+X*T^4/(T*X₀) := by
    have ht2 : 2 ≤ T^2 := by nlinarith
    have ht4 : 2*T^2 ≤ T^4 := by nlinarith [sq_nonneg (T^2-2)]
    have hprod : T*(T*X₀) ≤ X*T^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sq_nonneg (T^2))]
    have hh := (le_div_iff₀ (mul_pos hT0 hX₀)).mpr hprod
    linarith
  have hden : (1/(2*T))^2*T^(m+3) ≤
      (min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3) := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hmin 2)
      (pow_le_pow_left₀ hT0.le hfreq (m+3)) (by positivity) (by positivity)
  have h₃ : (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤ 8/T^m := by
    calc
      _ ≤ (2*T)/((1/(2*T))^2*T^(m+3)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by rw [pow_add]; field_simp; ring
  have hc : 2*(2 : ℝ)^(m+3)+8 ≤ (2 : ℝ)^(m+10) := by
    have hm : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
    rw [pow_add,pow_add]
    norm_num
    nlinarith
  calc
    _ ≤ (2 : ℝ)^(m+3)/T^m + (2 : ℝ)^(m+3)/T^m + 8/T^m := add_le_add (add_le_add h₁ h₂) h₃
    _ = (2*(2 : ℝ)^(m+3)+8)/T^m := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)

def SecondSourceSupport {ι : Type*} [DecidableEq ι]
    (p : ι → O) (X M : ℝ) (x : SecondExpansionData ι) : Prop :=
  Disjoint x.sourceCommon x.overlap ∧
    primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem secondExpansionSource_singleton_zero_of_not_support
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (g W : 𝓢(ℝ, ℂ)) (X Y M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hs : ¬ SecondSourceSupport p X M x) :
    secondExpansionSource p hp hcop hg F Ψ m c d z {x}
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y = 0 := by
  by_cases hd : Disjoint x.sourceCommon x.overlap
  · have hb : ¬ primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M :=
      fun hb => hs ⟨hd,hb⟩
    have hz (N : Finset ι) :
        normalizedColumn p (fun A => g (columnLog p X A))
          (x.sourceCommon ∪ (x.overlap ∪ N)) = 0 := by
      by_contra hn
      have h := normalizedColumn_subset_norm_bound p hp g M X hX hgM
        x.sourceCommon (x.overlap ∪ N) (x.sourceCommon ∪ x.overlap)
        (Finset.union_subset_union Finset.Subset.rfl Finset.subset_union_left) hn
      rw [FirstPassCubeLabels.primeProductNorm_union p _ _ hd] at h
      exact hb h
    simp only [secondExpansionSource, Finset.sum_singleton]
    have hk : secondChildKernelPair p hp hcop hg F x.overlap
        (secondRayMinus Ψ z) (secondRayPlus Ψ z) m (secondExpansionQuotient p x) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
        x.frequency (-x.frequency)
        (secondSourcePairKernel p
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S))
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S)) W Y) = 0 := by
      unfold secondChildKernelPair
      apply Finset.sum_eq_zero
      intro N hN
      apply Finset.sum_eq_zero
      intro Q hQ
      simp only [secondSourcePairKernel, hz N, star_zero, zero_mul, zero_div, mul_zero]
    rw [hk]
    ring
  · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj
      (secondRayPlus Ψ z) m c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      (-x.frequency) (fun _ => 1) x.sourceCommon x.overlap (fun h => hd h.symm)
    rw [secondMaskQuotient_spec p x.divisor x.sourceCommon hE] at hz
    simp only [secondExpansionSource, Finset.sum_singleton,
      secondExpansionQuotient_of_subset p x hE, secondTotalWeight, secondCommonWeight, hz,
      mul_zero, zero_mul]

include hinj in

theorem secondExpansionSource_eq_supported
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (g W : 𝓢(ℝ, ℂ)) (X Y M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (s : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon) :
    secondExpansionSource p hp hcop hg F Ψ m c d z s
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y =
    secondExpansionSource p hp hcop hg F Ψ m c d z
      (s.filter (SecondSourceSupport p X M))
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y := by
  classical
  unfold secondExpansionSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : SecondSourceSupport p X M x
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hz := secondExpansionSource_singleton_zero_of_not_support
      p hp hcop hg hinj F Ψ m c d z g W X Y M hX hgM x (hE x hx) hs
    simpa only [secondExpansionSource, Finset.sum_singleton] using hz

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def normLogBin (u : ℝ) : ℕ := ⌊Real.log u⌋₊
def normLogScale (j : ℕ) : ℝ := Real.exp (j : ℝ)

lemma normLogScale_pos (j : ℕ) : 0 < normLogScale j := Real.exp_pos _
lemma normLogScale_ge_one (j : ℕ) : 1 ≤ normLogScale j :=
  Real.one_le_exp (by positivity)

lemma normLogBin_error (u : ℝ) (hu : 1 ≤ u) :
    0 ≤ Real.log (u / normLogScale (normLogBin u)) ∧
      Real.log (u / normLogScale (normLogBin u)) ≤ 1 := by
  rw [Real.log_div (by linarith) (normLogScale_pos _).ne', normLogScale, Real.log_exp]
  exact ⟨sub_nonneg.mpr (Nat.floor_le (Real.log_nonneg hu)),
    by have h := Nat.lt_floor_add_one (Real.log u); dsimp [normLogBin]; linarith⟩

lemma normLogBin_scale_bounds (u : ℝ) (hu : 1 ≤ u) :
    normLogScale (normLogBin u) ≤ u ∧
      u ≤ normLogScale (normLogBin u) * Real.exp 1 := by
  have hu0 : 0 < u := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr (Nat.floor_le (Real.log_nonneg hu))
    simpa only [Real.exp_log hu0, normLogScale, normLogBin] using h
  · have h := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log u)).le
    simpa only [Real.exp_log hu0, Real.exp_add, normLogScale, normLogBin] using h

lemma normLogBin_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normLogBin u ≤ normLogBin v := Nat.floor_mono (Real.log_le_log hu huv)

abbrev SecondLogIndex := ℕ × ℕ × ℕ

def secondLogE (j : SecondLogIndex) : ℝ := normLogScale j.1
def secondLogV (j : SecondLogIndex) : ℝ := normLogScale j.2.1
def secondLogK (j : SecondLogIndex) : ℝ := normLogScale j.2.2

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondLogIndex (D : Finset ι) (x : SecondExpansionData ι) : SecondLogIndex :=
  (normLogBin (primeProductNorm p x.divisor), normLogBin (primeProductNorm p x.overlap),
    normLogBin (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2))

omit [DecidableEq ι] in
lemma actualSecondRow_ne_zero (D E : Finset ι) (k : O) (hk : k ≠ 0) :
    actualSecondRow p D E k ≠ 0 :=
  mul_ne_zero (mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)) hk

lemma element_norm_ge_one (a : O) (ha : a ≠ 0) : 1 ≤ ‖eisEmbedding a‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {a}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm jLabel)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondBaseLabel (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂

include hp in
omit [DecidableEq ι] in
lemma secondBaseLabel_ne_zero (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    secondBaseLabel p B C v₁ v₂ ε₁ ε₂ ≠ 0 := by
  apply mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact pow_ne_zero _ (hp i)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportNewLabel_norm (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) :
    (Ideal.absNorm (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x)) : ℝ) =
      ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 *
        primeProductNorm p x.divisor * primeProductNorm p x.overlap := by
  rw [← secondSupportLabel_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [secondSupportLabel, expansionSupportData, secondBaseLabel,
    map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm, primeProductNorm]

include hp in
omit [DecidableEq ι] in
lemma secondSupportNewLabel_ne_bot (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) :
    secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x) ≠ ⊥ := by
  rw [← secondSupportLabel_span, ne_eq, Ideal.span_singleton_eq_bot]
  exact mul_ne_zero (mul_ne_zero (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂)
    (primeSubsetGenerator_ne_zero _ _)) (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def secondLogBinBox (U K : ℝ) : Finset SecondLogIndex :=
  Finset.range (normLogBin U + 1) ×ˢ
    (Finset.range (normLogBin U + 1) ×ˢ Finset.range (normLogBin K + 1))

lemma secondLogBinBox_card (U K : ℝ) :
    (secondLogBinBox U K).card = (normLogBin U + 1)^2 * (normLogBin K + 1) := by
  simp only [secondLogBinBox, Finset.card_product, Finset.card_range]
  ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSourceSupport_bounds (X M : ℝ) (x : SecondExpansionData ι)
    (hx : SecondSourceSupport p X M x) (hE : x.divisor ⊆ x.sourceCommon) :
    primeProductNorm p x.sourceCommon ≤ X*Real.exp M ∧
    primeProductNorm p x.divisor ≤ X*Real.exp M ∧
    primeProductNorm p x.overlap ≤ X*Real.exp M := by
  have hG := (le_mul_of_one_le_right (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (primeProductNorm_ge_one p hp x.overlap)).trans hx.2
  have hV := (le_mul_of_one_le_left (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (primeProductNorm_ge_one p hp x.sourceCommon)).trans hx.2
  exact ⟨hG, (primeProductNorm_mono p hp hE).trans hG, hV⟩

include hp in
lemma secondLogIndex_mem_box (D : Finset ι) (X M K : ℝ) (x : SecondExpansionData ι)
    (hx : SecondSourceSupport p X M x) (hE : x.divisor ⊆ x.sourceCommon)
    (hk : x.frequency ≠ 0)
    (hK : ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ K) :
    secondLogIndex p D x ∈ secondLogBinBox (X*Real.exp M) K := by
  obtain ⟨hG,hE',hV⟩ := secondSourceSupport_bounds p hp X M x hx hE
  simp only [secondLogBinBox, secondLogIndex, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff]
  exact ⟨normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hE',
    normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hV,
    normLogBin_mono (by have h := element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk); linarith) hK⟩

def secondSupportedSector (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) : Finset (SecondExpansionData ι) :=
  (secondExpansionSector F (fun G E => (K G E).erase 0) R).filter (SecondSourceSupport p X M)

def secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) : Finset (SecondExpansionData ι) :=
  (secondSupportedSector p F K R X M).filter (fun x => secondLogIndex p D x = j)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_mem (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F K R X M) :
    x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
      x.frequency ≠ 0 ∧ x.frequency ∈ K x.sourceCommon x.divisor ∧
      x.sourceCommon \ x.divisor = R ∧ SecondSourceSupport p X M x := by
  obtain ⟨hx,hs⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hr⟩ := Finset.mem_filter.mp hx
  obtain ⟨hG,hE,hV,hk⟩ := (mem_secondExpansionPool _ _ _).mp hx
  obtain ⟨hk0,hk⟩ := Finset.mem_erase.mp hk
  exact ⟨hG,hE,hV,hk0,hk,hr,hs⟩

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogSector_subset (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    secondLogSector p D F K R X M j ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

include hp in

theorem sum_secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M Kmax : ℝ)
    (hK : ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax)
    (H : SecondExpansionData ι → ℂ) :
    (∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
      ∑ x ∈ secondLogSector p D F K R X M j, H x) =
      ∑ x ∈ secondSupportedSector p F K R X M, H x := by
  simp only [secondLogSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have hj := secondLogIndex_mem_box p hp D X M Kmax x hs hE hk0 (hK x hx)
  rw [Finset.sum_eq_single_of_mem (secondLogIndex p D x) hj]
  · simp
  · intro j hj hne
    simp [Ne.symm hne]

end SecondPassArithmetic

end

end OAI
