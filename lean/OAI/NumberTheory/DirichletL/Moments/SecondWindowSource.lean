import OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
import OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport
import OAI.NumberTheory.DirichletL.Moments.RestrictedWindow
import OAI.NumberTheory.DirichletL.Moments.LogDyadic
import OAI.NumberTheory.DirichletL.Moments.ConjugateWindow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentConjugateWindow

theorem star_logAnnulus (x : ℝ) : star (logAnnulus x)=logAnnulus x := by
  simp only [logAnnulus,Complex.star_def,Complex.conj_ofReal]

theorem star_logAnnulus_column (u t : ℝ) :
    star (columnPhase logAnnulus u t)=columnPhase logAnnulus u (-t) := by
  rw [star_columnPhase]
  simp only [star_logAnnulus]

end SevenEighths.CenteredMomentSecondWindowSource

end

end OAI
