import OAI.NumberTheory.DirichletL.Descent.SecondFreshAssembly
import OAI.NumberTheory.DirichletL.Descent.DensityAssembly
import OAI.NumberTheory.DirichletL.Inversion.SecondProfileUniform
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem balanced_density_integrable (g : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) :
    Integrable (InverseSecondProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) := by
  exact (full_density_integrable _ _ _ _).const_mul _

end
end SevenEighths.InverseMoment

end OAI
