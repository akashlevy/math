import OAI.NumberTheory.DirichletL.Eisenstein.LocalCutoffs
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

namespace CompletedGauss

section

open ActualEisensteinCubic

theorem two_pow_clog_le_double (n : ℕ) (hn : 1≤n) : 2^Nat.clog 2 n≤2*n := by
  by_cases h : n=1
  · simp [h]
  have hn1 : 1<n := lt_of_le_of_ne hn (Ne.symm h)
  have hl : 0<Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hn1
  have he : (Nat.clog 2 n).pred+1=Nat.clog 2 n := Nat.succ_pred_eq_of_pos hl
  calc
    _ = 2^(Nat.clog 2 n).pred*2 := by rw [←he,pow_succ]; rfl
    _ ≤ n*2 := Nat.mul_le_mul_right 2 hp.le
    _ = _ := Nat.mul_comm _ _

def completedRowDyad (rows : Finset (Ideal O)) (j : ℕ) : Finset (Ideal O) :=
  rows.filter (fun I => Nat.clog 2 (Ideal.absNorm I)=j)

def completedRowDyadicLength (K : ℝ) : ℕ := Nat.clog 2 ⌊K⌋₊

theorem completedRowDyad_bounds (rows : Finset (Ideal O)) (j : ℕ)
    (hrows : ∀I∈rows,I≠0) (I : Ideal O) (hI : I∈completedRowDyad rows j) :
    I≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^j := by
  obtain ⟨hIr,hj⟩ := Finset.mem_filter.mp hI
  have hn : 1≤Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (fun hz => hrows I hIr (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)
  have hl := two_pow_clog_le_double (Ideal.absNorm I) hn
  rw [hj] at hu hl
  refine ⟨hrows I hIr,?_,?_⟩
  · have hh : (2:ℝ)^j≤2*(Ideal.absNorm I:ℝ) := by exact_mod_cast hl
    linarith
  · exact_mod_cast hu

theorem completedRowDyad_sum {M : Type*} [AddCommMonoid M]
    (rows : Finset (Ideal O)) (K : ℝ) (hK : 0≤K)
    (hrows : ∀I∈rows,(Ideal.absNorm I:ℝ)≤K) (f : Ideal O→M) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),∑I∈completedRowDyad rows j,f I)=∑I∈rows,f I := by
  have hm : ∀I∈rows,Nat.clog 2 (Ideal.absNorm I)∈Finset.range (completedRowDyadicLength K+1) := by
    intro I hI
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.clog_mono_right 2 ((Nat.le_floor_iff hK).mpr (hrows I hI)))
  simpa only [completedRowDyad] using Finset.sum_fiberwise_of_maps_to hm f

theorem completedRowDyadic_top (K : ℝ) (hK : 1≤K) :
    (2:ℝ)^(completedRowDyadicLength K)≤2*K := by
  have hh := two_pow_clog_le_double ⌊K⌋₊ ((Nat.one_le_floor_iff K).mpr hK)
  have hr : (2:ℝ)^(completedRowDyadicLength K)≤2*(⌊K⌋₊:ℝ) := by exact_mod_cast hh
  exact hr.trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith : 0≤K)) (by norm_num))

theorem completedRowDyadic_scale (K : ℝ) (hK : 1≤K) (j : ℕ)
    (hj : j∈Finset.range (completedRowDyadicLength K+1)) : (2:ℝ)^j≤2*K :=
  (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans
    (completedRowDyadic_top K hK)

theorem completedRowDyadic_mass (K : ℝ) (hK : 1≤K) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),(2:ℝ)^j)≤4*K ∧
    (∑j∈Finset.range (completedRowDyadicLength K+1),((2:ℝ)^j)^2)≤16*K^2 := by
  have ht := completedRowDyadic_top K hK
  constructor
  · rw [geom_sum_eq (by norm_num : (2:ℝ)≠1),pow_succ]
    norm_num
    linarith
  · have he (j : ℕ) : ((2:ℝ)^j)^2=(4:ℝ)^j := by rw [←pow_mul,Nat.mul_comm j 2,pow_mul]; norm_num
    simp_rw [he]
    rw [geom_sum_eq (by norm_num : (4:ℝ)≠1),pow_succ,←he]
    norm_num
    have hp := pow_le_pow_left₀ (by positivity : 0≤(2:ℝ)^(completedRowDyadicLength K)) ht 2
    nlinarith

theorem completedRowDyadic_shape (s K X Q : ℝ) (hs : 0≤s) (hK : 1≤K)
    (hX : 0<X) (hQ : 0<Q) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),
      ((2:ℝ)^j*Q)^s*((2:ℝ)^j+((2:ℝ)^j)^2*Q/X))≤
      (16*(2:ℝ)^s)*(K*Q)^s*(K+K^2*Q/X) := by
  have hb (j : ℕ) (hj : j∈Finset.range (completedRowDyadicLength K+1)) :
      ((2:ℝ)^j*Q)^s≤(2*(K*Q))^s := by
    apply Real.rpow_le_rpow (by positivity) _ hs
    have h := mul_le_mul_of_nonneg_right (completedRowDyadic_scale K hK j hj) hQ.le
    nlinarith
  calc
    _ ≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
      (2*(K*Q))^s*((2:ℝ)^j+((2:ℝ)^j)^2*Q/X) :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hb j hj) (by positivity))
    _ = (2*(K*Q))^s*((∑j∈Finset.range (completedRowDyadicLength K+1),(2:ℝ)^j)+
      (∑j∈Finset.range (completedRowDyadicLength K+1),((2:ℝ)^j)^2)*Q/X) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_mul]
    _ ≤ (2*(K*Q))^s*(4*K+16*K^2*Q/X) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (completedRowDyadic_mass K hK).1
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (completedRowDyadic_mass K hK).2 hQ.le) hX.le)
    _ ≤ (2*(K*Q))^s*(16*(K+K^2*Q/X)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ = 4*K+16*(K^2*Q/X) := by ring
        _ ≤ 16*(K+K^2*Q/X) := by linarith
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring

open CanonicalQuadraticSieve

def HasExactCompletedDyadicModels (rays : ℕ) (rows : Finset (Ideal O))
    (K X ρ q levelBound : ℝ) (F Q : Ideal O) (W : ℝ→ℂ) (Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ) : Prop :=
  ∀j∈Finset.range (completedRowDyadicLength K+1),
    HasExactCompletedModels rays (completedRowDyad rows j) ((2:ℝ)^j) X ρ q levelBound F Q W Ψ lengthScale

end
section

open CompletedDyadic

def completedRamifiedStep : ℝ := (3:ℝ)^(1/3:ℝ)

theorem completedRamifiedStep_gt_one : 1<completedRamifiedStep := by
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

theorem cusp_coefficient_normalization (m n b : ℝ) (hn : 0<n) (hb : 0<b) :
    (3:ℝ)^(m/6)*Real.sqrt b/Real.sqrt ((3:ℝ)^m*n*b^3)=
      1/((3:ℝ)^(m/3)*Real.sqrt n*b) := by
  have hroot : Real.sqrt ((3:ℝ)^m)=(3:ℝ)^(m/6)*(3:ℝ)^(m/3) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hbroot : Real.sqrt (b^3)=b*Real.sqrt b := by
    rw [show b^3=b^2*b by ring,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq hb.le]
  rw [Real.sqrt_mul (mul_nonneg (by positivity) hn.le),Real.sqrt_mul (by positivity),hroot,hbroot]
  have hr1 : (3:ℝ)^(m/6)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr2 : (3:ℝ)^(m/3)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hbn : Real.sqrt b≠0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  field_simp

end

open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

namespace InitialMeanSquare

section
open ActualEisensteinCubic SecondPassArithmetic
open CanonicalQuadraticSieve (Admissible)

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def initialSquarefreeSector (s : Finset (SecondExpansionData ι)) : Finset (SecondExpansionData ι) :=
  s.filter (fun x => Squarefree (Ideal.span {(sourceObservation p x).2}))

theorem initial_weight_squarefree (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hw : secondArithmeticWeight p hp hcop hg Ψ m 1 1 ray x ≠ 0) :
    Squarefree (Ideal.span {(sourceObservation p x).2}) := by
  have hs := secondArithmeticWeight_squarefree p hp hcop hg Ψ m 1 1 ray x hE
    (by simp : Squarefree (Ideal.span {(1 : O)})) hw
  rw [sourceLabel_span]
  simpa using hs

theorem initial_source_eq_squarefree (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (F : Finset ι) (s : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s H₁ H₂ W Y =
      secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (initialSquarefreeSector p s) H₁ H₂ W Y := by
  unfold secondExpansionSource initialSquarefreeSector
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : Squarefree (Ideal.span {(sourceObservation p x).2})
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hw : secondArithmeticWeight p hp hcop hg Ψ m 1 1 ray x=0 := by
      by_contra hn
      exact hs (initial_weight_squarefree p hp hcop hg Ψ m ray x (hE x hx) hn)
    unfold secondArithmeticWeight at hw
    rcases mul_eq_zero.mp hw with h1 | h2
    · rw [h1]
      ring
    · rw [h2]
      ring

include hp hg in
omit [DecidableEq ι] in
theorem initial_squarefree_label_admissible
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (x : SecondExpansionData ι) (hs : Squarefree (Ideal.span {(sourceObservation p x).2})) :
    Admissible (Ideal.span {(sourceObservation p x).2}) := by
  have hn : (sourceObservation p x).2 ≠ 0 :=
    mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hnI : Ideal.span {(sourceObservation p x).2} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr hn
  refine ⟨hnI,hs,?_⟩
  intro P hP
  obtain ⟨hprime,hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hnI).mp hP
  rw [sourceLabel_span] at hdiv
  have hfactor (S : Finset ι) (hd : P ∣ ∏ i ∈ S,Ideal.span {p i}) :
      lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 := by
    obtain ⟨i,hi,hPi⟩ := (hprime.dvd_finsetProd_iff (fun i => Ideal.span {p i})).mp hd
    have hpi : Prime (Ideal.span {p i}) :=
      Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
    have he := (prime_dvd_prime_iff_eq hprime hpi).mp hPi
    rw [he]
    exact ⟨hg i,hc i⟩
  rcases hprime.dvd_or_dvd hdiv with h1 | h2
  · exact hfactor _ h1
  · exact hfactor _ h2

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

theorem initial_subbin_transfer
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (Z H M : ℝ) (j : SecondLogIndex)
        (s : Finset (SecondExpansionData ι)),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        s ⊆ secondLogSector p ∅ F K R Z M j →
        let X := initialLogColumn Z (primeProductNorm p R) j
        let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
        ∃ B : Frequency → ℝ,
          (∀ q, 0 ≤ B q) ∧
          (∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) W H‖ ≤
          (C*H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
            (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_sector_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F R Ψ m ray K Z H M j s hZ hH hΨ hsub
  dsimp only
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let X := initialLogColumn Z (primeProductNorm p R) j
  have hR : 0 < primeProductNorm p R := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hs : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
      (secondLogSector_subset p ∅ F K R Z M j (hsub hx))
  have hk : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp (hsub hx)).1).2.2.2.1
  have hcoords := initial_sector_coordinates p hp F R K Z M hZ j
  obtain ⟨B,hB,hdec,hbound⟩ := ht p hp hcop hg hinj hc hpr F Ψ m r ray s Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) hZ hH
    (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) hΨ hs hk
    (fun x hx => (hcoords x (hsub hx)).1) (fun x hx => (hcoords x (hsub hx)).2.1)
    (fun x hx => (hcoords x (hsub hx)).2.2.1) (fun x hx => (hcoords x (hsub hx)).2.2.2)
  refine ⟨B,hB,?_,?_⟩
  · simpa only [X, initial_log_radial Z H (primeProductNorm p R) hZ.ne' hR.ne'] using hdec
  · simpa only [r, elementNorm, primeSubsetGenerator_norm_eq_productNorm] using hbound

end InitialMeanSquare

namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

end InitialMeanSquare

end

end OAI
