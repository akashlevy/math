import OAI.NumberTheory.DirichletL.CubicSieve.RayCoefficients
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

section
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (activeGaussRowFactor)

theorem masked_pair_second_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S T : Finset ι) (hd : Disjoint S T)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let n := ∏ i : activeSupport T S, p i.val
    (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S z) *
      W (‖eisEmbedding z‖ ^ 2 / Y)) =
    ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding e‖ ^ 2 : ℝ)) *
          ∑' k : O, paperRadialFourier W
            (Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
              activeGaussRowFactor p hp hinj hg T S e k := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let Q := activePrimes P T S
  let q : activeSupport T S → O := fun i => p i.val
  let hQ := activePrimes_pairwise_isCoprime P hinj T S
  let j := activeExponent T S
  let row := finiteSexticRow Q (fun i => hg i.val) j
  let n := ∏ i, q i
  have hr (z : O) : star (finiteSquarefreeRow P hg T z) * finiteSquarefreeRow P hg S z = row z := by
    rw [finiteSquarefreeRow_pair_activeSupport]
    simp [Finset.disjoint_iff_inter_eq_empty.mp hd.symm, rowCoprimeMask, row, Q, j]
  have h := canonical_masked_radial_poisson_collected P hinj M Q hQ
    (fun i => hg i.val) (fun i => hc i.val) j
    (activeExponent_ne_zero T S) (activeExponent_lt_six T S) W Y hY
  have hn : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding n‖ :=
    GaussGeneratorTransport.finitePrimeModulus_norm_eq_product q
  dsimp only at h
  rw [hn] at h
  have ht := GaussGeneratorTransport.gauss_weighted_finite_radial_sum_transport
    q (fun i => hp i.val) hQ (fun i => hg i.val) j M.powerset
    (fun E => let e := primeSubsetGenerator P E
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row e /
        (‖eisEmbedding e‖ ^ 2 : ℝ))
    (fun E t => let e := primeSubsetGenerator P E
      paperRadialFourier W (Y * t / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)))
  calc
    _ = ∑' z : O, rowCoprimeMask P M z * row z * W (‖eisEmbedding z‖ ^ 2 / Y) := by
      apply tsum_congr
      intro z
      rw [hr]
    _ = ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        (canonicalNormalizedGauss Q hQ (fun i => hg i.val) j *
          ∑ E ∈ M.powerset,
            ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row (primeSubsetGenerator P E) /
              (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 : ℝ)) *
            ∑' k : O, star (row k) * paperRadialFourier W
              (Y * ‖eisEmbedding k‖ ^ 2 /
                (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))) := by
      rw [h]
      ring
    _ = _ := by
      rw [ht]
      simp only [Finset.mul_sum, ← tsum_mul_left]
      apply Finset.sum_congr rfl
      intro E hE
      apply tsum_congr
      intro k
      dsimp only [activeGaussRowFactor]
      ring

end

open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (columnLog primeProductNorm firstDualScale normalizedColumn)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondGaussTerm (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) S *
    secondInputCoefficient p hg Ψ₁ (m * (e * r)) c d H₁ S) *
  (supportMobius (fun i => Ideal.span {p i}) T *
    secondInputCoefficient p hg Ψ₂ (m * (e * r)) c d H₂ T) *
    activeGaussRowFactor p hp hinj hg T S e k

end

section

section

end

open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (firstDualScale firstLogDensity primeProductNorm_pos)

end

section

open SecondPassFiber (OldTuple newLabel newRow Valid)

theorem second_energy_selected_family {κ : Type*} [Fintype κ] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ)
      (P : κ → Ideal O × O → ℂ) (sel : OldTuple → κ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (sel x) (newLabel x, newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : κ, ∑ z ∈ t, ‖P u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := SecondPassFiber.second_energy_pushforward ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale P sel hb0 hB hL hvalid hmap ht hnorm hw
  calc
    _ ≤ ∑ x ∈ s, ‖w x‖ * ∑ u : κ, ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum
        (s := Finset.univ) (a := sel x)
        (f := fun u : κ => ‖P u (newLabel x, newRow x)‖ ^ 2)
        (fun u _ => sq_nonneg _) (Finset.mem_univ (sel x))
    _ = ∑ u : κ, ∑ x ∈ s, ‖w x‖ * ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ u : κ, B * C * (lengthScale * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P u z‖ ^ 2 := by
      exact Finset.sum_le_sum (fun u _ => hb s t b0 w (P u) B lengthScale hb0 hB hL hvalid hmap ht hnorm hw)
    _ = _ := by rw [Finset.mul_sum]

end

open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)

local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem exists_label_unit (f : O) (I : Ideal O) (hf : Ideal.span {f} = I) :
    ∃ u : Oˣ, f = (u : O) * idealGenerator I := by
  have hs : Ideal.span {idealGenerator I} = Ideal.span {f} := (span_idealGenerator I).trans hf.symm
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (f y : O) : ℂ :=
  ∑ N ∈ F.powerset, secondChildColumn p hp hcop hg Ψ m f y H N

def idealChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (u : Oˣ) (z : Ideal O × O) : ℂ :=
  fixedChildRow p hp hcop hg F Ψ m H ((u : O) * idealGenerator z.1)
    (if negative then -z.2 else z.2)

theorem idealChildRow_unit_energy_le (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (t : Finset (Ideal O × O)) (E : ℝ)
    (hE : ∀ u : Oˣ, (∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2) ≤ E) :
    (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2) ≤ 6 * E := by
  have hc : Fintype.card Oˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  calc
    _ ≤ ∑ u : Oˣ, E := Finset.sum_le_sum (fun u _ => hE u)
    _ = _ := by simp [hc]

end SecondPassArithmetic

end

end OAI
