import OAI.NumberTheory.DirichletL.RowCompletion.ZeroFreeRegion

/-!
# The spine, part 0: the objects of the argument

This file fixes the notation of the paper (§1.4 and §3 of
`preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf`) and states the two
intermediate bounds that the argument passes along, as named propositions:

* `MeanSquareBound` — Proposition 3.1 (`thm:ms`, the mean square of the sextic family, `ϑ = 1/10`);
* `SavingBound`     — Proposition 3.2 (`prop:extraction`, a power saving for the totient-weighted
  Möbius sum).

The whole development is specialised to the trivial character, i.e. to `ζ`.
-/

namespace OAI.QRH

open OAI

/-- `O = ℤ[ω]`, realised as the ring of integers of `ℚ(ζ₃)`. -/
abbrev O : Type := ActualEisensteinCubic.O

/-- The trivial Dirichlet character (modulus `1`): working with it is working with `ζ`. -/
noncomputable abbrev χ₁ : DirichletCharacter ℂ 1 := 1

/-- The excluded primes `S`: the prime ideals dividing the fixed level `2592 = 2⁵·3⁴` of the
twisted theta functions, i.e. the primes above `2` and `3`. -/
noncomputable def S : Finset (Ideal O) := CanonicalRowCompletion.reflectionExcludedPrimes 1

theorem bad_subset_S : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S :=
  CanonicalRowCompletion.reflectionExcludedPrimes_bad 1

theorem S_prime : ∀ P ∈ S, Prime P :=
  CanonicalRowCompletion.reflectionExcludedPrimes_prime 1

/-- The nonzero ideals of norm at most `M` that are prime to `S`. The cutoff `M` only has to
exceed the support of the weight; none of the sums below depends on it. -/
noncomputable def ideals (M : ℕ) : Finset (Ideal O) :=
  ConcretePrimeRowBridge.outsideIdealsUpTo S M

/-- The sextic family (paper (2.2), `eq:intro-family`):
`A_u(D) = ∑_{(𝔫, S) = 1} μ(𝔫) χ_𝔫(u) W(N𝔫 / D)`, where `χ_𝔫(u) = (u/𝔫)₆` is the sextic
residue symbol, extended by zero when `𝔫` and `u` are not coprime. -/
noncomputable def A (W : ℝ → ℂ) (D : ℝ) (M : ℕ) (u : O) : ℂ :=
  ConcretePrimeRowBridge.idealRowSum (ideals M)
    (ConcretePrimeRowBridge.outsideIdealsUpTo_ne_bot S M)
    (InitialMeanSquare.outside_good S M bad_subset_S) χ₁ (fun n => W (n / D)) u

/-- The totient-weighted Möbius sum (paper (3.1), `eq:A-phi`):
`A^φ(D) = ∑_{(𝔫, S) = 1} μ(𝔫) (φ(𝔫)/N𝔫) W(N𝔫 / D)`. Averaging the rows `u = b⁶` produces this
sum rather than the plain Möbius sum, because `χ_𝔫(b⁶)` detects coprimality of `b` and `𝔫`. -/
noncomputable def weightedSum (W : ℝ → ℂ) (D : ℝ) (M : ℕ) : ℂ :=
  ∑ I ∈ ideals M, ShortDraftHeckeBridge.baseChangeWeight χ₁ I * W ((Ideal.absNorm I : ℝ) / D) *
    SixthPowerAverage.totientDensity I

/-- **Mean-square bound** (paper Proposition 3.1, with `ϑ = 1/10`): for rows `u` of norm at
most `D^{1+ϑ} = D^{11/10}`,
`∑_u |A_u(D)|² ≪_ε D^{2+ϑ+ε} = D^{21/10+ε}`. -/
def MeanSquareBound (W : ℝ → ℂ) (b ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (D : ℝ), 1 ≤ D → b * D ≤ M → ∀ T : Finset O,
    (∀ u ∈ T, u ≠ 0 ∧ (Ideal.absNorm (Ideal.span {u}) : ℝ) ≤ D ^ ((11 : ℝ) / 10)) →
    ∑ u ∈ T, ‖A W D M u‖ ^ 2 ≤ C * D ^ ((21 : ℝ) / 10 + ε)

/-- **Power saving** (paper Proposition 3.2, `prop:extraction`): `A^φ(D) ≪_ε D^{23/24+ε}`. -/
def SavingBound (W : ℝ → ℂ) (b ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (D : ℝ), 1 ≤ D → b * D ≤ M →
    ‖weightedSum W D M‖ ≤ C * D ^ ((23 : ℝ) / 24 + ε)

end OAI.QRH
