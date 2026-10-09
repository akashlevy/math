import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
import OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergySourceInputReindexGates
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceInputReindex CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSecondInputGates CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstChildProfileControl CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalChildEnergy
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

section Dictionary
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

end Dictionary

theorem active_map (e : α≃β) (s : Input α) :
    activeInput (reindex e s)=reindex e (activeInput s) := rfl

end SevenEighths.CenteredMomentEnergySourceInputReindexGates

end

end OAI
