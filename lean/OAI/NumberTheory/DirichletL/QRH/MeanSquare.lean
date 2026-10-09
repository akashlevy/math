import OAI.NumberTheory.DirichletL.QRH.Setup

/-!
# The spine, part 3: the mean square of the sextic family (paper Proposition 3.1)

`∑_{0 < N(u) ≤ D^{11/10}} |A_u(D)|² ≪_ε D^{21/10+ε}`, proved as in the paper:

* `poissonReduction` (paper §4, Proposition 4.5, `prop:poisson-reduction`): Poisson summation in
  the row `u`, followed by
  the Gauss–Jacobi identities, reduces the mean square to a bound for the dual mean squares with
  cubic Gauss-sum coefficients (`HasInitialCanonicalDensityAtRadius`);
* `dualBound` (paper §5, Proposition 5.1, `prop:canonical`): that bound holds; it is proved by the
  finite descent
  over the cube index, using the completed mean square (Proposition 5.2, from the theta
  reflection and the quadratic large sieve) and the transfer (Proposition 5.4, `prop:transfer`).

The paper-numbered milestones inside these two steps are listed in `OAI/NumberTheory/DirichletL/QRH/Milestones.lean`.
-/

namespace OAI.QRH

open OAI
open scoped ContDiff

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The reflection input (paper Proposition 6.2, `lem:reflection`): the completed sums attached to
every row
shell are given exactly by the twisted cubic theta transformation, at the level `2592 q`. -/
theorem thetaModels :
    CanonicalRowCompletion.HasCanonicalThetaModels (S q)
      (InitialMeanSquare.conjugateMonoid (InitialMeanSquare.normCharacter χ)) 1
      CompletedGauss.completedRamifiedStep
      (CubicEisenstein.fixedCuspLevelBound (CanonicalRowCompletion.reflectionConductor q)) :=
  CanonicalRowCompletion.hasCanonicalThetaModels_of_fixed_shell_models _ _ _ _ _ _ _
    (CanonicalRowCompletion.actual_fixedShellModels q (NeZero.ne q) χ)

/-- **Proposition 5.1** (`prop:canonical`, the dual mean squares after the descent): the dual mean
squares with
cubic Gauss-sum coefficients have square-root cancellation, `≪ D^δ (XF)²`, in the ranges
produced by the Poisson reduction. -/
theorem dualBound : InitialMeanSquare.HasInitialCanonicalDensityAtRadius χ (S q) (bad_subset_S q) :=
  CanonicalRowCompletion.hasInitialCanonicalDensityAtRadius_of_theta χ (S q) (S_prime q)
    (bad_subset_S q) 1 _ _ one_pos CompletedGauss.completedRamifiedStep_gt_one
    (CanonicalRowCompletion.reflectionLevelBound_ge_one q (NeZero.ne q)) (thetaModels χ)

omit [NeZero q] in
/-- **Proposition 4.5** (`prop:poisson-reduction`, Poisson reduction): the dual bound implies the
mean square, for every
row range `D^{1+σ}` with `σ > 1/20`; we use `σ = ϑ = 1/10`. -/
theorem poissonReduction
    (hdual : InitialMeanSquare.HasInitialCanonicalDensityAtRadius χ (S q) (bad_subset_S q))
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (ε : ℝ) (hε : 0 < ε) :
    MeanSquareBound χ W b ε := by
  obtain ⟨C, hC, h⟩ := InitialMeanSquare.outside_mean_square_of_canonical_density_at_radius χ (S q)
    (bad_subset_S q) (S_prime q) hdual W a b ha hs hW ((1 : ℝ) / 10) ε (by norm_num) hε
  refine ⟨C, hC, fun M D hD hM T hT => ?_⟩
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD
  have hpow : D * D ^ (1 + (1 : ℝ) / 10) * D ^ ε = D ^ ((21 : ℝ) / 10 + ε) := by
    rw [← Real.rpow_one_add' hDpos.le (by norm_num), ← Real.rpow_add hDpos]
    norm_num
  calc ∑ u ∈ T, ‖A χ W D M u‖ ^ 2
      ≤ C * D * D ^ (1 + (1 : ℝ) / 10) * D ^ ε :=
        h M D hD hM T
          (fun u hu => by rw [show (1 : ℝ) + 1 / 10 = 11 / 10 by norm_num]; exact (hT u hu).2)
          (fun u hu => (hT u hu).1)
    _ = C * D ^ ((21 : ℝ) / 10 + ε) := by rw [← hpow]; ring

/-- **Proposition 3.1** (`thm:ms`, mean square, `ϑ = 1/10`). -/
theorem meanSquare (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (ε : ℝ) (hε : 0 < ε) :
    MeanSquareBound χ W b ε :=
  poissonReduction χ (dualBound χ) W a b ha hs hW ε hε

end OAI.QRH
