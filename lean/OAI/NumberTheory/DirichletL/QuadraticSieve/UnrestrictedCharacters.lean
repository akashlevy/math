import OAI.NumberTheory.DirichletL.CubicSieve.ResidualSectors
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

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

def unrestrictedPairCharacter (I J lengthScale : Ideal O) : ℂ :=
  quadraticRow I (idealGenerator lengthScale) * quadraticRow J (idealGenerator lengthScale)

theorem unrestrictedPairCharacter_span (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (z : O) :
    unrestrictedPairCharacter I J (Ideal.span {z}) = quadraticRow I z * quadraticRow J z := by
  have ha : Associated (idealGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_idealGenerator _)
  obtain ⟨u, hu⟩ := ha
  have hv := canonical_pair_unit_invariant I J hI hJ hray u (idealGenerator (Ideal.span {z}))
  have he : u.val * idealGenerator (Ideal.span {z}) = z := by simpa only [mul_comm] using hu
  rw [he] at hv
  exact hv.symm

theorem unrestrictedPairCharacter_mul (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A B : Ideal O) :
    unrestrictedPairCharacter I J (A * B) =
      unrestrictedPairCharacter I J A * unrestrictedPairCharacter I J B := by
  have hs : Ideal.span {idealGenerator A * idealGenerator B} = A * B := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_idealGenerator, span_idealGenerator]
  rw [← hs, unrestrictedPairCharacter_span I J hI hJ hray]
  rw [canonical_quadraticRow_argument_mul I hI, canonical_quadraticRow_argument_mul J hJ]
  unfold unrestrictedPairCharacter
  ring

theorem unrestrictedPairCharacter_eq_primary (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (lengthScale : Ideal O) (hL : Supported lengthScale) :
    unrestrictedPairCharacter I J lengthScale =
      quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale) := by
  have hz := PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors lengthScale hL.1
    (fun P hP => (hL.2 P hP).1)
  have h := unrestrictedPairCharacter_span I J hI hJ hray (primaryGenerator lengthScale)
  rw [(primaryGenerator_spec lengthScale hz).1] at h
  exact h

open EisensteinSchwartzPoisson UnrestrictedIdealReindex GaussGeneratorTransport

theorem idealGenerator_norm_sq (lengthScale : Ideal O) :
    ‖eisEmbedding (idealGenerator lengthScale)‖ ^ 2 = (Ideal.absNorm lengthScale : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, span_idealGenerator]

theorem canonical_pair_fourier_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun h : O => (quadraticRow I h * quadraticRow J h) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W t ht)
  intro h
  simp only [norm_mul]
  calc
    _ ≤ (1 * 1) * ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
      gcongr
      · exact quadraticRow_norm_le_one I h
      · exact quadraticRow_norm_le_one J h
    _ = _ := by ring

theorem canonical_nonprincipal_dual_ideal_reindex
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hnt : I ≠ 1 ∨ J ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    (∑' h : O, (quadraticRow I h * quadraticRow J h) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) =
      (6 : ℂ) * ∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I J lengthScale.val *
        paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) := by
  let f : O → ℂ := fun h => (quadraticRow I h * quadraticRow J h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hf : Summable f := canonical_pair_fourier_summable I J W t ht
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [quadratic_pair_zero_of_nontrivial I J hI hJ hnt, zero_mul]
  have hu (u : Oˣ) (z : O) : f (u.val * z) = f z := by
    dsimp only [f]
    rw [canonical_pair_unit_invariant I J hI hJ hray, norm_eisEmbedding_unit_mul]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  simpa only [f, idealGenerator_norm_sq, unrestrictedPairCharacter] using he

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

def fixedBadPrimes : Finset (Ideal O) := {Ideal.span {lambda}, Ideal.span {(2 : O)}}

theorem prime_good_iff_not_bad (P : Ideal O) [P.IsMaximal] :
    (lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2) ↔ P ∉ fixedBadPrimes := by
  constructor
  · rintro ⟨hl, hc⟩ hp
    rcases Finset.mem_insert.mp hp with hp | hp
    · exact hl (hp ▸ Ideal.subset_span (by simp))
    · have he : P = Ideal.span {(2 : O)} := Finset.mem_singleton.mp hp
      exact hc (he ▸ twoIdeal_characteristic)
  · intro hp
    constructor
    · intro hl
      have he := maximal_ideal_eq_span_of_mem P inferInstance lambda lambdaIdeal_maximal hl
      exact hp (he ▸ Finset.mem_insert_self _ _)
    · intro hc
      have ht : (2 : O) ∈ P := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hz : (2 : O ⧸ P) = 0 := (ringChar.spec (O ⧸ P) 2).mpr (by rw [hc])
        simpa only [map_ofNat] using hz
      have he := maximal_ideal_eq_span_of_mem P inferInstance (2 : O) twoIdeal_maximal ht
      exact hp (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

def badPrimeSupport (I : Ideal O) : Finset (Ideal O) := IdealMobiusDivisorSum.primeSupport I ∩ fixedBadPrimes

def goodPrimeSupport (I : Ideal O) : Finset (Ideal O) := IdealMobiusDivisorSum.primeSupport I \ fixedBadPrimes

def goodSquarefreePart (I : Ideal O) : Ideal O := ∏ P ∈ goodPrimeSupport I, P

theorem badPrimeSupport_subset (I : Ideal O) : badPrimeSupport I ⊆ fixedBadPrimes :=
  Finset.inter_subset_right

theorem goodSquarefreePart_admissible (I : Ideal O) : Admissible (goodSquarefreePart I) := by
  have hs : goodPrimeSupport I ⊆ IdealMobiusDivisorSum.primeSupport I := Finset.sdiff_subset
  refine ⟨support_product_ne_zero hs, squarefree_support_product hs, ?_⟩
  intro P hP
  change P ∈ UniqueFactorizationMonoid.normalizedFactors (∏ Q ∈ goodPrimeSupport I, Q) at hP
  rw [factors_support_product hs] at hP
  have hp : P ∈ goodPrimeSupport I := hP
  have hprime := support_prime (hs hp)
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  exact (prime_good_iff_not_bad P).mpr (Finset.mem_sdiff.mp hp).2

theorem squarefree_bad_good_product (I : Ideal O) (hI : Squarefree I) :
    (∏ P ∈ badPrimeSupport I, P) * goodSquarefreePart I = I := by
  have hu : badPrimeSupport I ∪ goodPrimeSupport I = IdealMobiusDivisorSum.primeSupport I := by
    ext P
    simp only [badPrimeSupport, goodPrimeSupport, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hd : Disjoint (badPrimeSupport I) (goodPrimeSupport I) := by
    apply Finset.disjoint_left.mpr
    intro P hp hq
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2
  rw [goodSquarefreePart, ← Finset.prod_union hd, hu]
  exact squarefree_support_product_self hI

theorem unrestrictedPairCharacter_squarefree_bad_split
    (I J B : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hB : Squarefree B) :
    unrestrictedPairCharacter I J B =
      unrestrictedPairCharacter I J (∏ P ∈ badPrimeSupport B, P) *
        (quadraticRow I (primaryGenerator (goodSquarefreePart B)) *
          quadraticRow J (primaryGenerator (goodSquarefreePart B))) := by
  conv_lhs => rw [← squarefree_bad_good_product B hB]
  rw [unrestrictedPairCharacter_mul I J hI hJ hray,
    unrestrictedPairCharacter_eq_primary I J hI hJ hray _
      (admissible_supported (goodSquarefreePart_admissible B))]

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge

theorem fixedBadPrimes_card : fixedBadPrimes.card = 2 := by
  have hn : (Ideal.span {lambda} : Ideal O) ≠ Ideal.span {(2 : O)} := by
    intro h
    have hb : badPrime false = badPrime true := h
    have := badPrime_injective hb
    cases this
  simp [fixedBadPrimes, hn]

theorem fixedBadPrimes_powerset_card : fixedBadPrimes.powerset.card = 4 := by
  rw [Finset.card_powerset, fixedBadPrimes_card]
  norm_num

def badPrimeSector (I : Ideal O) : fixedBadPrimes.powerset :=
  ⟨badPrimeSupport I, Finset.mem_powerset.mpr (badPrimeSupport_subset I)⟩

theorem goodSquarefreePart_injective_on_sector (I J : Ideal O) (hI : Squarefree I) (hJ : Squarefree J)
    (hs : badPrimeSector I = badPrimeSector J) (hg : goodSquarefreePart I = goodSquarefreePart J) : I = J := by
  have he : badPrimeSupport I = badPrimeSupport J := congrArg Subtype.val hs
  calc
    I = (∏ P ∈ badPrimeSupport I, P) * goodSquarefreePart I := (squarefree_bad_good_product I hI).symm
    _ = (∏ P ∈ badPrimeSupport J, P) * goodSquarefreePart J := by rw [he, hg]
    _ = J := squarefree_bad_good_product J hJ

theorem goodSquarefreePart_norm_le (I : Ideal O) (hI : Squarefree I) :
    Ideal.absNorm (goodSquarefreePart I) ≤ Ideal.absNorm I := by
  have hd : goodSquarefreePart I ∣ I := by
    exact ⟨∏ P ∈ badPrimeSupport I, P, (squarefree_bad_good_product I hI).symm.trans (mul_comm _ _)⟩
  apply Nat.le_of_dvd
  · exact Nat.pos_iff_ne_zero.mpr (fun hn => hI.ne_zero (Ideal.absNorm_eq_zero_iff.mp hn))
  · exact map_dvd Ideal.absNorm hd

theorem goodSquarefreePart_mem_idealRange (I : Ideal O) (hI : Squarefree I) (M : ℝ)
    (hM : (Ideal.absNorm I : ℝ) ≤ M) : goodSquarefreePart I ∈ idealRange M := by
  apply mem_idealRange.mpr
  exact ⟨goodSquarefreePart_admissible I, (Nat.cast_le.mpr (goodSquarefreePart_norm_le I hI)).trans hM⟩

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open FiniteSieveOperator

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex

def originalPairIdealDualKernel (D I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  let I' := idealQuotient D I
  let J' := idealQuotient D J
  let n := primaryGenerator I' * primaryGenerator J'
  let χ := fun z => quadraticRow I' z * quadraticRow J' z
  let R := fun P : gcdMaskPrimes D => P.val
  ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      let d := primeSubsetGenerator R E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I' J' lengthScale.val * paperRadialFourier W
        (M * (Ideal.absNorm lengthScale.val : ℝ) / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

theorem originalPairDualKernel_eq_ideal
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    originalPairDualKernel D I J W M = originalPairIdealDualKernel D I J W M := by
  let Q := idealQuotient D I
  let T := idealQuotient D J
  let n := primaryGenerator Q * primaryGenerator T
  let R := fun P : gcdMaskPrimes D => P.val
  let χ := fun z => quadraticRow Q z * quadraticRow T z
  let a := fun E : Finset (gcdMaskPrimes D) =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ (primeSubsetGenerator R E) /
      (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 : ℝ)
  let f := fun E : Finset (gcdMaskPrimes D) => ∑' h : O, χ h * paperRadialFourier W
    (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  let g := fun E : Finset (gcdMaskPrimes D) => ∑' lengthScale : NonzeroIdeal,
    unrestrictedPairCharacter Q T lengthScale.val * paperRadialFourier W
      (M * (Ideal.absNorm lengthScale.val : ℝ) / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  have hQ : Admissible Q := admissible_idealQuotient hI hDI
  have hT : Admissible T := admissible_idealQuotient hJ hDJ
  have hn0 : n ≠ 0 := mul_ne_zero
    (supported_primaryGenerator_ne_zero Q (admissible_supported hQ))
    (supported_primaryGenerator_ne_zero T (admissible_supported hT))
  have hn : 0 < ‖eisEmbedding n‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hn0)
  have hfg (E : Finset (gcdMaskPrimes D)) : f E = 6 * g E := by
    have hd : 0 < ‖eisEmbedding (primeSubsetGenerator R E)‖ :=
      norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero R E))
    let X := M / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)
    have hX : 0 < X := div_pos hM (mul_pos (sq_pos_of_pos hd) (sq_pos_of_pos hn))
    have he := canonical_nonprincipal_dual_ideal_reindex Q T hQ hT
      (columnRay_idealQuotient_eq D I J hI hJ hDI hDJ hray)
      (residual_pair_nontrivial D I J hDI hDJ hIJ) W X hX
    have harg (r : ℝ) : X * r =
        M * r / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) := by
      dsimp only [X]
      ring
    simpa only [harg, f, g, χ] using he
  have hs : (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * f E) =
      6 * ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * g E := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E _
    rw [hfg]
    ring
  change ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * f E) =
    ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * g E)
  rw [hs]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel UnrestrictedIdealReindex

theorem unrestrictedPairCharacter_square
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A : Ideal O) :
    unrestrictedPairCharacter I J (A ^ 2) =
      idealZeroMask I (idealGenerator A) * idealZeroMask J (idealGenerator A) := by
  rw [pow_two, unrestrictedPairCharacter_mul I J hI hJ hray]
  unfold unrestrictedPairCharacter
  calc
    _ = (quadraticRow I (idealGenerator A) * quadraticRow I (idealGenerator A)) *
      (quadraticRow J (idealGenerator A) * quadraticRow J (idealGenerator A)) := by ring
    _ = _ := by rw [canonical_quadraticRow_squared I hI, canonical_quadraticRow_squared J hJ]

end CanonicalQuadraticSieve

namespace JointLogSeparation
open FourierBridge FirstPassCubeLabels

theorem joint_separation_twisted_profiles {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ a₃ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ y : ι → ℝ,
        (∏ j, V j (y j)) * (frequencyTwist g₁ θ₁) (∑ j, a₁ j * y j) * (frequencyTwist g₂ θ₂) (∑ j, a₂ j * y j) *
          EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp (∑ j, a₃ j * y j)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          (∏ j, V j (y j)) * logPhase t₁ (∑ j, a₁ j * y j) *
            logPhase t₂ (∑ j, a₂ j * y j) * logPhase t₃ (∑ j, a₃ j * y j) *
            ((𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃‖ ≤
        C * (1 + ‖θ₁‖)^(J+2) * (1 + ‖θ₂‖)^(J+2) *
          firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  classical
  obtain ⟨C₃, hC₃, hsep⟩ := EisensteinSchwartzPoisson.paperRadialFourier_log_separation_envelope
    W V a₃ M hM hV A (J + 2)
  let C₁ := fourierPointBound (J + 2) (twistSourceBound g₁ (J + 2))
  let C₂ := fourierPointBound (J + 2) (twistSourceBound g₂ (J + 2))
  have hC₁ : 0 ≤ C₁ := fourierPointBound_nonneg _ _ (twistSourceBound_nonneg _ _)
  have hC₂ : 0 ≤ C₂ := fourierPointBound_nonneg _ _ (twistSourceBound_nonneg _ _)
  refine ⟨C₁ * C₂ * C₃, by positivity, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  let A₁ := frequencyTwist g₁ θ₁
  let A₂ := frequencyTwist g₂ θ₂
  refine ⟨?_, ?_, AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J |>.congr ?_⟩
  · intro y
    let P : ℂ := ∏ j, V j (y j)
    let s₁ : ℝ := ∑ j, a₁ j * y j
    let s₂ : ℝ := ∑ j, a₂ j * y j
    let s₃ : ℝ := ∑ j, a₃ j * y j
    have hr : P * EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp s₃) =
        ∫ t, P * logPhase t s₃ * b t := by
      have hh := hb y
      simpa only [Finset.prod_mul_distrib, ← logPhase_sum, P, s₃] using hh
    exact joint_separation_identity A₁ A₂ b P
      (EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp s₃)) s₁ s₂ s₃ hr
  · intro t₁ t₂ t₃
    have hr₁ := firstLogDensity_nonneg J t₁
    have hr₂ := firstLogDensity_nonneg J t₂
    have hr₃ := firstLogDensity_nonneg J t₃
    have hb₃ : (1 + R) ^ A * ‖b t₃‖ ≤ C₃ * firstLogDensity J t₃ := by
      rw [firstLogDensity, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t₃‖) (J + 2))).mpr
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hpoint t₃
    have h₁ := twisted_profile_fourier_envelope g₁ θ₁ t₁ J
    have h₂ := twisted_profile_fourier_envelope g₂ θ₂ t₂ J
    simp only [norm_mul]
    calc
      _ = ‖(𝓕 (frequencyTwist g₁ θ₁)) t₁‖ * ‖(𝓕 (frequencyTwist g₂ θ₂)) t₂‖ * ((1 + R)^A * ‖b t₃‖) := by ring
      _ ≤ (C₁ * (1 + ‖θ₁‖)^(J+2) * firstLogDensity J t₁) *
          (C₂ * (1 + ‖θ₂‖)^(J+2) * firstLogDensity J t₂) * (C₃ * firstLogDensity J t₃) := by
        apply mul_le_mul
        · exact mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
        · exact hb₃
        · positivity
        · positivity
      _ = _ := by ring
  · filter_upwards [] with t
    simp

end JointLogSeparation

end

end OAI
