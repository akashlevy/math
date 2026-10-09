import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
namespace OAI

namespace SevenEighths.Probe
noncomputable section

def principalScalar {ι : Type*} (slots : Finset ι) (Z ℓ : ℝ) (S : ι → ℝ) : ℝ :=
  (-1) ^ slots.card * Z ^ (-ℓ / 6) * ∏ i ∈ slots, S i

theorem principalScalar_ne_zero {ι : Type*} (slots : Finset ι)
    {Z ℓ : ℝ} {S : ι → ℝ} (hZ : 0 < Z)
    (hS : ∀ i ∈ slots, 0 < S i) : principalScalar slots Z ℓ S ≠ 0 := by
  unfold principalScalar
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ne_of_gt (Real.rpow_pos_of_pos hZ _))
  · exact ne_of_gt (Finset.prod_pos hS)

end
end SevenEighths.Probe

end OAI
