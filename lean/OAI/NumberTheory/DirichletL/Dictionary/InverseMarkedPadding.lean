import OAI.NumberTheory.DirichletL.Dictionary.InverseRawRadial
import OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalSlots
import OAI.NumberTheory.DirichletL.Hecke.DetectorRawFiber
import OAI.NumberTheory.DirichletL.Descent.Basic
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseMarkedPadding
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection ConcreteTraceCRT CanonicalQuadraticSieve ActualEisensteinCubic
local notation "O" => HeckeFamily.O

def radialMajorant : 𝓢(ℝ,ℂ) :=
  Classical.choose DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant

theorem radialMajorant_nonneg (x : ℝ) : 0≤(radialMajorant x).re :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.1 x

theorem radialMajorant_one (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) : radialMajorant x=1 :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.2 x hx

end SevenEighths.DetectorDictionaryInverseMarkedPadding

end

end OAI
