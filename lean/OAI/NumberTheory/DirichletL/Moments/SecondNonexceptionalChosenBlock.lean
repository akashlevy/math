import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalPhysical
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost
import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic

def canonicalRadial (τ:Character)(Q:Ideal O)(n:Fin 4→ℤ):Radial:=
  sourceRadial (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow τ Q fixedBadMask 1 z)
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)

lemma sourceRadial_eq_canonical {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (hm:m≠0)(hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)(n:Fin 4→ℤ):
    sourceRadial (nonexceptional η χ Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))
      ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)=
      canonicalRadial (τ χ) Q n:=by
  have he:nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z):=by
    funext z
    exact propext (h.nonexceptional_iff χ Q m z hm hml hm2)
  simp only [canonicalRadial,he]

end SevenEighths.CenteredMomentSecondNonexceptionalChosenBlock

end

end OAI
