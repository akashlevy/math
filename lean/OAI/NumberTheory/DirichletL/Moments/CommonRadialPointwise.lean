import OAI.NumberTheory.DirichletL.Moments.CommonRadialSource
import OAI.NumberTheory.DirichletL.Moments.CommonRadialCost
import OAI.NumberTheory.DirichletL.Moments.RadialPointwiseUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialSource CenteredMomentCommonRadialData CenteredMomentCommonRadialCost
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

 def profileCost (s:Input ι) : ℝ :=
  ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)*s.toData.profileFactor

omit [DecidableEq ι] in
lemma profileCost_nonneg (s:Input ι) : 0≤profileCost s :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) s.toData.profile_nonneg

end SevenEighths.CenteredMomentCommonRadialPointwise

end

end OAI
