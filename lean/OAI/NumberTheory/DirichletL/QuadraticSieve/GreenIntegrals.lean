import OAI.NumberTheory.DirichletL.QuadraticSieve.MiddleWindows
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

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_double_sum_real_factor_fun {n p : Type*} [Fintype n] [Fintype p]
    (u z : n → p → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z j k)‖ = c * ‖∑ j, ∑ k, u j k * z j k‖ := by
  have he : (∑ j, ∑ k, u j k * ((c : ℂ) * z j k)) =
      (c : ℂ) * ∑ j, ∑ k, u j k * z j k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O)
    (left : n → Ideal O) (right : p → Ideal O) (M F : ℝ) (h : O)
    (d : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  ((Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def dualProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j * right k then
      originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualProductDivisorMiddleAt W K rows left right a b M F P h := by
  classical
  unfold dualProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    dualProductDivisorMiddleAt W K rows left right a b M F P h ≤
      dualMiddleWindowAt W S T rows left right a b M F (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i j k => dualPrincipalKernel W rows left right M F h d i j k)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [dualMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold dualPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor_fun _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.dual_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hs := hexp.dual_middle_pool deltaLoss hδ ε hε S T B N M F U hB hN hM hF hU
    (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2))
    (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := dualProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M F P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => dualProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M F P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end CanonicalQuadraticSieve

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc in
theorem secondChildColumn_norm_le_test (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m f y : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondChildColumn p hp hcop hg Ψ m f y H S‖ ≤ ‖H S‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) S m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondChildColumn,norm_mul,norm_pow,columnCoefficient_norm_one p hp hcop hg hc]
  calc
    _ ≤ 1 * 1 * 1 * 1^4 * 1 * ‖H S‖ := by
      gcongr <;> first
        | exact hΨ _
        | exact hm
        | exact finiteSquarefreeRow_norm_le_one _ hg S f
        | exact finiteSquarefreeRow_norm_le_one _ hg S y
    _ = _ := by ring

include hc in

theorem fixedChildRow_elementary
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m f y : O) (H : Finset ι → ℂ) (X M : ℝ) (hX : 1 ≤ X) (hM : 0 ≤ M)
    (hH : ∀ S, ‖H S‖ ≤ M) (hSupp : ∀ S, H S ≠ 0 → primeProductNorm p S ≤ X) :
    ‖fixedChildRow p hp hcop hg F Ψ m H f y‖ ≤ 128 * X * M := by
  have heq : fixedChildRow p hp hcop hg F Ψ m H f y =
      ∑ S ∈ boundedPrimeSupports p F X, secondChildColumn p hp hcop hg Ψ m f y H S := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hHS : H S = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hS,hSupp S h⟩)
    simp only [secondChildColumn,hHS,mul_zero]
  rw [heq]
  calc
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, ‖secondChildColumn p hp hcop hg Ψ m f y H S‖ := norm_sum_le _ _
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, M :=
      Finset.sum_le_sum (fun S hS => (secondChildColumn_norm_le_test p hp hcop hg hc Ψ hΨ m f y H S).trans (hH S))
    _ = ((boundedPrimeSupports p F X).card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F X hX) hM

end SecondPassArithmetic

namespace DescentFiberCost
open ActualEisensteinCubic ConcreteTraceCRT
open ShortDraftLatticeCount ActualEisensteinCoordinates

theorem finite_element_count_real (S : Finset O) (K : ℝ) (hK : 1 ≤ K)
    (hS : ∀ z ∈ S, ‖eisEmbedding z‖^2 ≤ K) : (S.card : ℝ) ≤ 128*K := by
  have hbound : ∀ z ∈ S, q (coords z) ≤ (⌊K⌋₊ : ℕ) := by
    intro z hz
    have hq : (qNat z : ℝ) ≤ K := by
      rw [qNat_eq_absNorm_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
      exact hS z hz
    have hn := Nat.le_floor hq
    have he : (qNat z : ℤ) = q (coords z) := Int.toNat_of_nonneg (qO_nonneg z)
    rw [← he]
    exact_mod_cast hn
  have hcard := actual_eisenstein_count S ⌊K⌋₊ hbound
  have hr : (S.card : ℝ) ≤ 64*((⌊K⌋₊ : ℝ)+1) := by exact_mod_cast hcard
  have hf : (⌊K⌋₊ : ℝ) ≤ K := Nat.floor_le (by linarith)
  linarith

theorem finite_label_row_count (T : Finset (Ideal O × O)) (F K : ℝ)
    (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hT : ∀ z ∈ T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖eisEmbedding z.2‖^2 ≤ K) :
    (T.card : ℝ) ≤ 128^2 * F * K := by
  let I := T.image Prod.fst
  let R := T.image Prod.snd
  have hI : (I.card : ℝ) ≤ 128*F := by
    apply finite_ideal_count_real I F hF
    · intro J hJ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hJ
      exact (hT z hz).1
    · intro J hJ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hJ
      exact (hT z hz).2.1
  have hR : (R.card : ℝ) ≤ 128*K := by
    apply finite_element_count_real R K hK
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    exact (hT z hz).2.2
  have hsub : T ⊆ I ×ˢ R := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  have hn := Finset.card_le_card hsub
  rw [Finset.card_product] at hn
  calc
    _ ≤ (I.card : ℝ) * R.card := by exact_mod_cast hn
    _ ≤ (128*F)*(128*K) := mul_le_mul hI hR (Nat.cast_nonneg _) (by linarith)
    _ = _ := by ring

end DescentFiberCost

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open FirstPassCubeLabels (primeProductNorm columnLog)

theorem childEnergy_elementary_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X F K A M a b : ℝ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (_hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV : ∀ s, ‖V s‖ ≤ M) (hVsupp : ∀ s, V s ≠ 0 → |s| ≤ A)
    (hT : ∀ z ∈ T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b / (X*F) ≤
      6 * 128^4 * K * (max 1 (X*Real.exp A))^2 * M^2 / X := by
  let H := fixedSecondTest p V X a b testNegative
  let Y := max 1 (X*Real.exp A)
  have hX0 : 0 < X := hX
  have hF0 : 0 < F := by linarith
  have hY : 1 ≤ Y := le_max_left _ _
  have hH : ∀ S, ‖H S‖ ≤ M := by
    intro S
    cases testNegative <;>
      simpa only [H,fixedSecondTest,Bool.false_eq_true,ite_false,ite_true,
        fixedColumnTest,norm_mul,norm_star,FourierBridge.logPhase_norm,mul_one] using hV (columnLog p X S)
  have hSupp : ∀ S, H S ≠ 0 → primeProductNorm p S ≤ Y := by
    intro S hS
    have hv : V (columnLog p X S) ≠ 0 := by
      intro hz
      apply hS
      cases testNegative <;> simp [H,fixedSecondTest,fixedColumnTest,hz]
    exact (columnLog_norm_upper p hp X A hX0 S ((le_abs_self _).trans (hVsupp _ hv))).trans
      (le_max_right _ _)
  have hrow (f y : O) : ‖fixedChildRow p hp hcop hg pool Ψ m H f y‖ ≤ 128*Y*M :=
    fixedChildRow_elementary p hp hcop hg hc hinj pool Ψ hΨ m f y H Y M hY hM hH hSupp
  have hu (u : Oˣ) : (∑ z ∈ T, ‖idealChildRow p hp hcop hg pool Ψ m H rowNegative u z‖^2) ≤
      (T.card : ℝ) * (128*Y*M)^2 := by
    calc
      _ ≤ ∑ z ∈ T, (128*Y*M)^2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact pow_le_pow_left₀ (norm_nonneg _) (hrow _ _) 2
      _ = _ := by simp
  have he := idealChildRow_unit_energy_le p hp hcop hg pool Ψ m H rowNegative T
    ((T.card : ℝ)*(128*Y*M)^2) hu
  change childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b ≤ _ at he
  have ht := DescentFiberCost.finite_label_row_count T F K hF hK hT
  apply (div_le_iff₀ (mul_pos hX0 hF0)).mpr
  calc
    _ ≤ 6*((T.card : ℝ)*(128*Y*M)^2) := he
    _ ≤ 6*((128^2*F*K)*(128*Y*M)^2) := by gcongr
    _ = (6*128^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*(X*F) := by
      dsimp [Y]
      field_simp

end SecondPassIntegration

namespace ShortDraftLatticeCount
open ActualEisensteinCubic ActualEisensteinCoordinates ConcreteTraceCRT

theorem rowNormBall_norm_sq_le (H : ℕ) (k : ActualEisensteinCubic.O) (hk : k ∈ rowNormBall H) :
    ‖eisEmbedding k‖^2 ≤ 3*((H : ℝ)+1)^2 := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hv
  obtain ⟨haL,haU⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hbL,hbU⟩ := Finset.mem_Icc.mp hb
  have ha2 : v.1^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haU) (show 0 ≤ (H : ℤ)+1+v.1 by linarith)]
  have hb2 : v.2^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbU) (show 0 ≤ (H : ℤ)+1+v.2 by linarith)]
  have hq : v.1*v.1-v.1*v.2+v.2*v.2 ≤ 3*((H : ℤ)+1)^2 := by
    nlinarith [sq_nonneg (v.1+v.2)]
  rw [eisEmbedding_eval_norm_sq]
  exact_mod_cast hq

end ShortDraftLatticeCount
namespace SecondPassArithmetic
open ActualEisensteinCubic ConcreteTraceCRT

theorem secondFrequencyCutoff_norm_sq_le (scale H : ℝ) (k : ActualEisensteinCubic.O)
    (hk : k ∈ secondFrequencyCutoff scale H) :
    ‖eisEmbedding k‖^2 ≤ 3*((⌈H/scale⌉₊ : ℝ)+1)^2 :=
  ShortDraftLatticeCount.rowNormBall_norm_sq_le _ k hk

end SecondPassArithmetic

namespace CubicEisenstein

lemma axisSlice_update (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) :
    axisSlice f (Function.update p j t) j = axisSlice f p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

end CubicEisenstein

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT

end CubicEisenstein

end

end OAI
