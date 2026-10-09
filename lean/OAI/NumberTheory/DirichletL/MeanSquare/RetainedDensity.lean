import OAI.NumberTheory.DirichletL.MeanSquare.CanonicalDensity
namespace OAI

noncomputable section

namespace InitialMeanSquare

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

section

open SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)

lemma initialLogLabel_ge_one (j : SecondLogIndex) : 1 ≤ initialLogLabel j :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))

lemma initialLogColumn_pos (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 < Z) (hB : 0 < B) :
    0 < initialLogColumn Z B j :=
  div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hB)

lemma initialLogColumn_le (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 ≤ Z) (hB : 1 ≤ B) :
    initialLogColumn Z B j ≤ Z := div_le_self hZ
  (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _)) hB)

lemma initialLogLabel_cap (U Kmax : ℝ) (hU : 1 ≤ U) (j : SecondLogIndex)
    (hj : j ∈ secondLogBinBox U Kmax) : initialLogLabel j ≤ U^2*Real.exp 2 := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin Kmax+1 := by
    simpa only [secondLogBinBox,Finset.mem_product,Finset.mem_range] using hj
  have he : secondLogE j ≤ U := by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogE normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.1
  have hv : secondLogV j ≤ U := by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogV normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.1
  unfold initialLogLabel
  simpa only [pow_two] using mul_le_mul_of_nonneg_right
    (mul_le_mul he hv (normLogScale_pos _).le (zero_le_one.trans hU)) (Real.exp_pos 2).le

theorem initial_radial_invariant (Z B c σ θ deltaLoss κ : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hB : 0 < B) (hc : 0 ≤ c) (hcZ : c ≤ Z^deltaLoss)
    (hmargin : deltaLoss+θ ≤ σ-κ)
    (hrad : initialRadial Z (Z^(1+σ)) B j ≤ Z^θ) :
    (secondLogK j*Real.exp 2)*(c*B) ≤
      initialLogColumn Z B j*initialLogLabel j*Z^(-κ) := by
  have hZ0 := zero_lt_one.trans_le hZ
  have hH : 0 < Z^(1+σ) := Real.rpow_pos_of_pos hZ0 _
  have hm : 0 < initialLogColumn Z B j*initialLogLabel j := by
    rw [initial_log_mass Z B hB.ne' j]
    positivity
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    rw [show -σ=(1 : ℝ)-(1+σ) by ring,Real.rpow_sub hZ0,Real.rpow_one]
  have hid : (secondLogK j*Real.exp 2)*(c*B)/(initialLogColumn Z B j*initialLogLabel j)=
      c*(Z/(Z^(1+σ)))*(Z^(1+σ)*secondLogK j*B^2/Z^2) := by
    rw [initial_log_mass Z B hB.ne' j]
    have hE := (Real.exp_pos (2 : ℝ)).ne'
    have hz := hZ0.ne'
    have hh := hH.ne'
    field_simp

  rw [mul_comm (initialLogColumn Z B j*initialLogLabel j)]
  apply (div_le_iff₀ hm).mp
  rw [hid,he]
  calc
    c*Z^(-σ)*(Z^(1+σ)*secondLogK j*B^2/Z^2) ≤ c*Z^(-σ)*Z^θ :=
      mul_le_mul_of_nonneg_left hrad (mul_nonneg hc (Real.rpow_nonneg hZ0.le _))
    _ ≤ Z^deltaLoss*Z^(-σ)*Z^θ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcZ (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hZ0.le _)
    _ = Z^(deltaLoss-σ+θ) := by rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]; congr 1
    _ ≤ Z^(-κ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem initial_large_threshold (a b c deltaLoss : ℝ) (hc : 1 ≤ c) (hδ : 0 < deltaLoss) :
    ∃ Z0 : ℝ,1 ≤ Z0 ∧ ∀ Z : ℝ,Z0 ≤ Z →
      Real.exp 2 ≤ Z ∧ c*Real.exp (initialErrorWindow a b) ≤ Z ∧
      initialPolynomialCap a b*Real.exp 2 ≤ Z ∧
      (Real.exp (initialErrorWindow a b))^2*Real.exp 2 ≤ Z ∧ c ≤ Z^deltaLoss := by
  let M := initialErrorWindow a b
  let Q := initialPolynomialCap a b
  let Z0 := 1+Real.exp 2+c*Real.exp M+Q*Real.exp 2+(Real.exp M)^2*Real.exp 2+c^(1/deltaLoss)
  have hc0 := (zero_lt_one.trans_le hc).le
  have hQ := initialPolynomialCap_ge_one a b
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have he2 := Real.exp_pos (2 : ℝ)
  have heM := Real.exp_pos M
  have hr : 0 ≤ c^(1/deltaLoss) := Real.rpow_nonneg hc0 _
  have hp : 0 ≤ (Real.exp M)^2*Real.exp 2 := by positivity
  have hcp : 0 ≤ c*Real.exp M := by positivity
  have hqp : 0 ≤ Q*Real.exp 2 := by positivity
  have hZ0 : 1 ≤ Z0 := by dsimp [Z0]; linarith
  refine ⟨Z0,hZ0,?_⟩
  intro Z hZ
  have hzroot : c^(1/deltaLoss) ≤ Z := by dsimp [Z0] at hZ; linarith
  have hroot : (c^(1/deltaLoss))^deltaLoss=c := by
    rw [←Real.rpow_mul hc0]
    have hd : (1/deltaLoss)*deltaLoss=1 := by field_simp
    rw [hd,Real.rpow_one]
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp [Z0] at hZ; linarith
  · change c*Real.exp M ≤ Z; dsimp [Z0] at hZ; linarith
  · change Q*Real.exp 2 ≤ Z; dsimp [Z0] at hZ; linarith
  · change (Real.exp M)^2*Real.exp 2 ≤ Z; dsimp [Z0] at hZ; linarith
  · rw [←hroot]
    exact Real.rpow_le_rpow hr hzroot hδ.le

theorem initial_large_bin_geometry {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (F R : Finset ι) (a b Z σ θ deltaLoss c : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hc : 1 ≤ c)
    (hR : R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)))
    (hj : j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b))
      (initialErrorRowBound a b Z (Z^(1+σ))))
    (hσ : 0 ≤ σ) (hmargin : deltaLoss+θ ≤ σ-(1 : ℝ)/20)
    (hlarge : Real.exp 2 ≤ Z ∧ c*Real.exp (initialErrorWindow a b) ≤ Z ∧
      initialPolynomialCap a b*Real.exp 2 ≤ Z ∧
      (Real.exp (initialErrorWindow a b))^2*Real.exp 2 ≤ Z ∧ c ≤ Z^deltaLoss)
    (hrad : initialRadial Z (Z^(1+σ)) (primeProductNorm p R) j ≤ Z^θ) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let lengthScale := initialLogLabel j
    let K := secondLogK j*Real.exp 2
    X ≤ Z^20 ∧ lengthScale ≤ Z^20 ∧ K ≤ Z^20 ∧ c*primeProductNorm p R ≤ Z^20 ∧
      X*lengthScale ≤ Z^2 ∧ K*(c*primeProductNorm p R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) := by
  dsimp only
  have hZ0 := zero_lt_one.trans_le hZ
  have hB := primeProductNorm_ge_one p hp R
  have hBp := zero_lt_one.trans_le hB
  have hU : 1 ≤ Z*Real.exp (initialErrorWindow a b) := one_le_mul_of_one_le_of_one_le hZ
    (Real.one_le_exp (by unfold initialErrorWindow; positivity))
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
  have hBcap := (Finset.mem_filter.mp hR).2
  have hKcap := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
  have hKbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
    (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
  have hL := initialLogLabel_cap _ _ hU j hj
  have hp20 (n : ℕ) (hn : n ≤ 20) : Z^n ≤ Z^20 := pow_le_pow_right₀ hZ hn
  have hinv := initial_radial_invariant Z (primeProductNorm p R) c σ θ deltaLoss
    ((1 : ℝ)/20) j hZ hBp (zero_le_one.trans hc) hlarge.2.2.2.2 hmargin hrad
  rw [show -((1 : ℝ)/20)=(-1 : ℝ)/20 by ring] at hinv
  refine ⟨?_,?_,?_,?_,?_,hinv⟩
  · exact (initialLogColumn_le Z _ j hZ0.le hB).trans (by simpa using hp20 1 (by decide))
  · apply hL.trans
    calc
      _ = ((Real.exp (initialErrorWindow a b))^2*Real.exp 2)*Z^2 := by ring
      _ ≤ Z*Z^2 := mul_le_mul_of_nonneg_right hlarge.2.2.2.1 (sq_nonneg Z)
      _ ≤ Z^20 := by simpa [pow_succ,mul_comm] using hp20 3 (by decide)
  · calc
      _ ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
        mul_le_mul_of_nonneg_right (hKbin.trans hKcap) (Real.exp_pos _).le
      _ = (initialPolynomialCap a b*Real.exp 2)*Z^17 := by ring
      _ ≤ Z*Z^17 := mul_le_mul_of_nonneg_right hlarge.2.2.1 (pow_nonneg hZ0.le _)
      _ ≤ Z^20 := by simpa [pow_succ,mul_comm] using hp20 18 (by decide)
  · calc
      _ ≤ c*(Z*Real.exp (initialErrorWindow a b)) := mul_le_mul_of_nonneg_left hBcap (zero_le_one.trans hc)
      _ = (c*Real.exp (initialErrorWindow a b))*Z := by ring
      _ ≤ Z*Z := mul_le_mul_of_nonneg_right hlarge.2.1 hZ0.le
      _ ≤ Z^20 := by simpa [pow_two] using hp20 2 (by decide)
  · rw [initial_log_mass Z (primeProductNorm p R) hBp.ne' j]
    calc
      _ ≤ Z*Real.exp 2 := mul_le_mul_of_nonneg_right (div_le_self hZ0.le hB) (Real.exp_pos _).le
      _ ≤ Z^2 := by simpa [pow_two] using mul_le_mul_of_nonneg_left hlarge.1 hZ0.le

end

section

open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (firstLogDensity)

theorem initial_density_elementary_squared_mass {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (J : ℕ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤
      (initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3)*K*(X*lengthScale)^2 := by
  let C := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hC : 0 ≤ C := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hd := childDensity_elementary_all_scales p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X lengthScale K A Vmax J hX hL hK hA hVmax hV₁ hV₂ hs₁ hs₂ hT
  change _/(X*lengthScale) ≤ C*K*X at hd
  have hraw := (div_le_iff₀ (mul_pos hX (zero_lt_one.trans_le hL))).mp hd
  have hbase : 0 ≤ (C*K*X)*(X*lengthScale) := by positivity
  calc
    _ ≤ (C*K*X)*(X*lengthScale) := hraw
    _ ≤ ((C*K*X)*(X*lengthScale))*lengthScale := le_mul_of_one_le_right hbase hL
    _ = _ := by dsimp only [C]; ring

end

section

open ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

end

section

open SecondPassArithmetic

theorem initial_log_harmonic_small_power (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ,0 < C ∧ ∀ (Y U Kmax : ℝ),1 ≤ Y → 0 < U → 0 < Kmax → U ≤ Y → Kmax ≤ Y →
      ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Y^η := by
  obtain ⟨C,hC,hbound⟩ := globalLogFactor_small_power η hη
  refine ⟨128*Real.exp 1*C,by positivity,?_⟩
  intro Y U Kmax hY hU hK hUY hKY
  let B := 1+Real.log 27+22*Real.log Y
  have hlog := Real.log_nonneg hY
  have h27 : 0 ≤ Real.log 27 := Real.log_nonneg (by norm_num)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hu := normLogBin_le_log_upper U Y hU hUY hY
  have hk := normLogBin_le_log_upper Kmax Y hK hKY hY
  have huB : (normLogBin U : ℝ)+1 ≤ B := by dsimp [B]; linarith
  have hkB : (normLogBin Kmax : ℝ)+1 ≤ B := by dsimp [B]; linarith
  have hcard : ((secondLogBinBox U Kmax).card : ℝ) ≤ B^3 := by
    rw [secondLogBinBox_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ B^2*B := mul_le_mul (pow_le_pow_left₀ (by positivity) huB 2) hkB (by positivity) (sq_nonneg B)
      _ = _ := by ring
  have hh : 128*Real.exp 1*(normLogBin U+1 : ℝ) ≤ 128*Real.exp 1*B :=
    mul_le_mul_of_nonneg_left huB (by positivity)
  calc
    _ ≤ B^3*(128*Real.exp 1*B) := mul_le_mul hcard hh (by positivity) (pow_nonneg (zero_le_one.trans hB) _)
    _ = 128*Real.exp 1*B^4 := by ring
    _ ≤ 128*Real.exp 1*B^10 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hB (by decide)) (by positivity)
    _ ≤ 128*Real.exp 1*(C*Y^η) := mul_le_mul_of_nonneg_left (hbound Y hY) (by positivity)
    _ = _ := by ring

theorem initial_row_log_budget (η Ccap : ℝ) (hη : 0 < η) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧ ∀ (Z U Kmax : ℝ),1 ≤ Z → 0 < U → 0 < Kmax →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      (Kmax*Real.exp 2)^η*((secondLogBinBox U Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Z^(34*η) := by
  obtain ⟨C,hC,hlog⟩ := initial_log_harmonic_small_power η hη
  refine ⟨C*(Real.exp 2)^η*Ccap^(2*η),by positivity,?_⟩
  intro Z U Kmax hZ hU hK hUY hKY
  have hZ0 := zero_lt_one.trans_le hZ
  have hcap0 := zero_lt_one.trans_le hcap
  let Y := Ccap*Z^17
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs := hlog Y U Kmax hY hU hK hUY hKY
  have hrow : (Kmax*Real.exp 2)^η ≤ (Y*Real.exp 2)^η := Real.rpow_le_rpow
    (mul_pos hK (Real.exp_pos _)).le (mul_le_mul_of_nonneg_right hKY (Real.exp_pos _).le) hη.le
  calc
    _ = (Kmax*Real.exp 2)^η*(((secondLogBinBox U Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin U+1 : ℝ))) := by ring
    _ ≤ (Y*Real.exp 2)^η*(C*Y^η) := mul_le_mul hrow hlogs (by positivity) (by positivity)
    _ = C*(Real.exp 2)^η*Y^(2*η) := by
      rw [Real.mul_rpow (zero_le_one.trans hY) (Real.exp_pos _).le]
      rw [show 2*η=η+η by ring,Real.rpow_add (zero_lt_one.trans_le hY)]
      ring
    _ = (C*(Real.exp 2)^η*Ccap^(2*η))*Z^(34*η) := by
      dsimp [Y]
      rw [Real.mul_rpow hcap0.le (pow_nonneg hZ0.le _),←Real.rpow_natCast_mul hZ0.le]
      norm_num
      ring_nf

end

section

open ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

end

open ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

end InitialMeanSquare

end

end OAI
