import OAI.NumberTheory.DirichletL.QRH.MeanSquare
import Batteries.Tactic.Alias

/-!
# The spine, part 4: where the paper's §§4–7 live in the formal proof

`OAI.QRH.meanSquare` (paper Proposition 3.1) is `poissonReduction ∘ dualBound`. This file names, in
the paper's numbering, the main results used inside those two steps, so that every proposition
of the paper has a Lean counterpart. All of them are proved (they are aliases of theorems of the
library) and all of them lie on the proof path of the main theorem.

The formal proof follows the strategy of the paper with different bookkeeping:

* test functions are compactly supported profiles `V(log(N𝔫/X))`, expanded in the height twists
  `N𝔫^{iθ}`, with bounds polynomial in `θ`, instead of `C^J`-norms (paper Appendix B);
* excluded primes are carried as a mask `m` inside the dual mean square, instead of being removed
  by Lemma 4.4 (`lem:remove-exclusions`);
* rows are weighted by a compactly supported smooth majorant, whose Fourier transform only decays
  rapidly, instead of a weight `Φ` with compactly supported Fourier transform;
* the descent removes cubes of norm `> D^{1/1000}` at each level and runs at most `3000` levels,
  carrying an explicit margin `1/20 - 3000η` for the accumulated losses, instead of the adaptive
  cutoff `H_c` and the induction on `j` of Proposition 5.1 (`prop:canonical`).
-/

namespace OAI.QRH

open OAI

/-- **Proposition 5.1** (`prop:canonical`, the descent): the dual energies satisfy `≪ D^ε (XF)²`
for every
canonical state (the parameter ranges of the paper, with the margin `1/20` and the mask `m`). -/
alias descent_bound := CanonicalRowCompletion.outsideLogEnergy_small_power

/-- The induction of Proposition 5.1 on the rank `⌈1000 log K / log D⌉ ≤ 3000`. -/
alias descent_by_rank := CanonicalRowCompletion.outsideLogEnergy_finite_rank

/-- **Lemma 5.3 + Proposition 5.4** (`lem:cube-reduction`, `prop:transfer`; one descent step): cube
inversion splits a state into short
cubes, bounded by the completed mean square, and long cubes, which the transfer bounds by
states of strictly smaller rank. -/
alias descent_step := CanonicalRowCompletion.canonicalLog_actual_step

/-- **Lemma 5.3, short cubes** (eq. (5.9), `eq:short-cube-bound`): cubes of norm `≤ D^{1/1000}` cost
`D^{7ε-1/40}(XF)²`. -/
alias short_cubes := CanonicalRowCompletion.canonicalShortState_uniform_twist

/-- **Proposition 5.4** (`prop:transfer`, the transfer by two Poisson summations): the long cubes
are bounded by
dual energies of strictly smaller rank. -/
alias transfer := SecondPassArithmetic.reopenedCanonicalRow_closed_step

/-- **Eq. (5.8)** (`eq:cube-inverse`, cube inversion): Möbius inversion over the cube index
recovers the squarefree
sum from the completed sums `T`. -/
alias cube_inversion := CompletedGauss.completed_cube_inverse

/-- **Proposition 5.2** (`prop:R`, the completed mean square): if the completed sums are given by
the theta
reflection, then `∑_{N(k) ≤ K} |T(X; Ψ_k)|² ≪ (K N(Q))^ε (K + K² N(Q)/X)`. -/
alias completed_mean_square := CompletedHeight.uniform_polynomial_mean_square_of_exact_reflection

/-- **Proposition 6.2** (`lem:reflection`, the twisted theta transformation, exact form): at the
fixed level of `ζ`,
every completed sum over a row shell equals a fixed scalar times a reflected dual sum. -/
alias theta_reflection := CanonicalRowCompletion.actual_fixedShellModels

/-- **Lemma 6.5** (`lem:quadratic`, the quadratic large sieve over `ℤ[ω]`, Input D): the norm of
the quadratic
character matrix with `M` rows and `N` columns is `≪ (MN)^ε (M + N)`. -/
alias quadratic_large_sieve := CanonicalQuadraticSieve.sieveNorm_sharp

/-- **Lemma 4.1, eq. (4.2)** (`lem:arithmetic`, `eq:gj`; Gauss–Jacobi): `γ₁(p)γ₂(p) =
\overline{χ_p(4)} γ₃(p) γ₂(p)³`. -/
alias gauss_jacobi := ActualEisensteinCubic.breveGamma1_gamma2_relation

/-- **Lemma 4.1, eq. (4.2)** (`eq:gj`; `J(χ², χ²) = -p`): `γ₂(p)³ = -α(p)`. -/
alias gauss_two_cube := ActualEisensteinCubic.breveGamma2_cube

/-- **Lemma 4.1, eq. (4.5)** (`eq:convert2`; `μ` is absorbed): the Möbius factor times the sextic
Gauss sum is a
cubic Gauss-sum coefficient times a fixed ray-class factor. -/
alias mobius_absorption := MixedGaussConversion.moebius_mixed_gauss_conversion

/-- **Lemma 4.2** (`lem:poisson`, Poisson summation with excluded primes, Input A). -/
alias poisson_with_exclusions := ActualEisensteinCubic.canonical_masked_radial_poisson_collected

/-- **Lemma 7.2** (`lem:arithmetic-poisson`, the second Poisson identity). -/
alias second_poisson := SecondPassArithmetic.masked_pair_second_poisson

/-- **Input C** (Kubota's cubic theta function): automorphy of the (averaged) cubic theta function
`θ_src` under the level-3 Kubota character. -/
alias theta_automorphy := CubicEisenstein.cubicSourceResidualFunction_automorphy

/-- **Input C** (Patterson's coefficients, eq. (2.10), `eq:intro-theta-coefficients`): the Fourier
coefficient of the cubic theta
function at a squarefree index times a cube. -/
alias theta_coefficients := CubicEisenstein.infinityCoefficient_squarefree_cube

/-- **Lemma 6.4** (`lem:theta-bounds`, support and size of the coefficients at the three cusps). -/
alias theta_cusp_bounds := CubicEisenstein.three_cusp_coefficients_squarefree_cube_bound

end OAI.QRH
