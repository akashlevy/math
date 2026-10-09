import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Covering.Quotient
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Order.PiLex
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.RingTheory.Multiplicity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Multiset.Interval
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
namespace OAI

open scoped BigOperators

namespace ShortDraft

abbrev EisensteinCoordinates := ℤ × ℤ

def eisensteinMul (x y : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def eisensteinNorm (x : EisensteinCoordinates) : ℤ :=
  x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem eisenstein_norm_mul (x y : EisensteinCoordinates) :
    eisensteinNorm (eisensteinMul x y) = eisensteinNorm x * eisensteinNorm y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  dsimp [eisensteinNorm, eisensteinMul]
  ring

theorem eisenstein_norm_nonneg (x : EisensteinCoordinates) :
    0 ≤ eisensteinNorm x := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]

end ShortDraft

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem gaussSum_mulShift_any (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (a : F) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : a = 0
  · subst a
    have hshift : ψ.mulShift (0 : F) = 1 := by
      ext x
      simp
    rw [hshift, gaussSum_one_right hχ]
    simp
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    simpa [hu.unit_spec] using gaussSum_mulShift_eq χ ψ hu.unit

theorem gaussSum_eq_units_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
  classical
  have hzero : χ (0 : F) * ψ (0 : F) = 0 := by simp
  calc
    gaussSum χ ψ = ∑ x ∈ (Finset.univ : Finset F).erase 0, χ x * ψ x := by
      simpa only [gaussSum, hzero, add_zero] using
        (Finset.sum_erase_add (Finset.univ : Finset F)
          (fun x => χ x * ψ x) (Finset.mem_univ (0 : F))).symm
    _ = ∑ x : {x : F // x ≠ 0}, χ x * ψ x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
        (fun y : Fˣ => χ (y : F) * ψ (y : F))
        (fun x : {x : F // x ≠ 0} => χ x * ψ x) ?_).symm
      intro y
      rfl

theorem additive_unit_sum (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (a : F) :
    (∑ y : Fˣ, ψ (a * (y : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hgauss : (∑ y : Fˣ, ψ (a * (y : F))) =
      gaussSum (1 : MulChar F ℂ) (ψ.mulShift a) := by
    rw [gaussSum_eq_units_sum]
    simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
  rw [hgauss]
  split_ifs with ha
  · subst a
    simp only [AddChar.mulShift_zero, gaussSum_one_one]
    exact_mod_cast (Nat.card_eq_fintype_card (α := Fˣ))
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    have hshift : ψ.mulShift a ≠ 1 := by
      intro heq
      exact hψ ((AddChar.mulShift_unit_eq_one_iff ψ hu).mp heq)
    exact gaussSum_one_left hshift

theorem sextic_fourth_mask (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hψ : ψ ≠ 1) (a : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hexp : ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = 1 := by
    calc
      ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = (χ ^ 6)⁻¹ := by group
      _ = 1 := by rw [hχ, inv_one]
  rw [hexp]
  simp only [MulChar.one_apply_coe, one_mul]
  calc
    (∑ h : Fˣ, ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ψ (a * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp
    _ = _ := additive_unit_sum ψ hψ a

theorem active_zero_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) (ε x : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
  classical
  have hquad : ((χ⁻¹) ^ 2)⁻¹ = χ ^ 2 := by group
  calc
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (χ ^ 2) (y : F) * ψ ((ε * x) * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
          rw [← hquad, MulChar.inv_apply', inv_inv]
    _ = gaussSum (χ ^ 2) (ψ.mulShift (ε * x)) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]
    _ = (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
      rw [gaussSum_mulShift_any (χ ^ 2) ψ hχ₂ (ε * x)]
      rw [map_mul]
      ring

theorem nontrivial_fourier_coefficient (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ t : F, χ t * ψ (-(h * t))) =
      χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) := by
  calc
    (∑ t : F, χ t * ψ (-(h * t))) =
        gaussSum χ ((ψ.mulShift (-1)).mulShift h) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) :=
      gaussSum_mulShift_any χ (ψ.mulShift (-1)) hχ h

theorem trivial_fourier_coefficient (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (h : F) :
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
      if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  calc
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
        gaussSum (1 : MulChar F ℂ) (ψ.mulShift (-h)) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = ∑ u : Fˣ, ψ ((-h) * (u : F)) := by
      rw [gaussSum_eq_units_sum]
      simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
    _ = if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
      simpa only [neg_eq_zero] using additive_unit_sum ψ hψ (-h)

end ShortDraftLocal

end OAI
