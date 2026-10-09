import OAI.NumberTheory.DirichletL.Reflection.OriginalBranchSum
import OAI.NumberTheory.DirichletL.Reflection.LiteralNormalized
import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
import OAI.NumberTheory.DirichletL.Reflection.CountBudget
import OAI.NumberTheory.DirichletL.Reflection.FullEnergyBasic
import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps
import OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy
import OAI.NumberTheory.DirichletL.Reflection.TupleMembers
import OAI.NumberTheory.DirichletL.Reflection.CanonicalParameters
import OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds
import OAI.NumberTheory.DirichletL.Reflection.DyadCompletionEnergy
import OAI.NumberTheory.DirichletL.Reflection.DyadBudget
import OAI.NumberTheory.DirichletL.Reflection.MemberChoiceTransport
import OAI.NumberTheory.DirichletL.Reflection.InactiveSource
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

lemma inactiveRows_mem {σ φ : Type*} [Fintype σ] [DecidableEq σ]
    (rows : Finset (Ideal Eis)) (lists : σ→Finset (Ideal Eis)) (T : Finset σ)
    (FF : φ→Ideal Eis) (b : ∀ i : {i // i∉T},lists i.val) (K : Ideal Eis) :
    K∈inactiveRowSet rows lists T FF b ↔ K∈rows ∧
      IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠FF j := by
  exact Finset.mem_filter

end
end SevenEighths.InverseReflectedPhase

end OAI
