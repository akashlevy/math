import OAI.NumberTheory.DirichletL.Hecke.PrimeRow
import OAI.NumberTheory.DirichletL.Hecke.RowNonprincipal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckePrimeNonprincipal
open HeckeFamily HeckeRowClosure CanonicalRowCompletion

theorem inverse_twist_elementCoeff (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n) (n : O) :
    elementCoeff ((χ.inverse.product θ).inverse) n =
      rowTwist (elementHom (η.product θ.inverse)) m f z n := by
  rw [elementCoeff_inverse,elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,hχ]
  change _ = elementCoeff (η.product θ.inverse) n * idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  change (elementCoeff θ n)⁻¹ *
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) = _
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

end SevenEighths.HeckePrimeNonprincipal

end

end OAI
