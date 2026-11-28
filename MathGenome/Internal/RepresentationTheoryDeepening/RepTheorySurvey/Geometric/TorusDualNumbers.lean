import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusDualNumbers
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeModels

namespace RepTheorySurvey.Geometric.TorusDualNumbers

noncomputable section

open LatticeModelSpecs (coset)
open TorusDualNumberSpecs

abbrev specialize := TorusDualNumberSpecs.specialize

abbrev infinitesimalLoop := TorusDualNumberSpecs.infinitesimalLoop

/-- The infinitesimal loop has a nontrivial coset which specializes to the identity. -/
theorem exampleProperties : Expected.ExampleProperties := by
  have hcoeff : (infinitesimalLoop : LaurentSeries A).coeff (-1) = DualNumber.eps := by
    change (1 + nilpotentTerm).coeff (-1 : ℤ) = _
    simp [nilpotentTerm, HahnSeries.coeff_add, HahnSeries.coeff_one]
  have heps : (DualNumber.eps : A) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg TrivSqZeroExt.snd h : (1 : ℂ) = 0)
  have hreduce : Units.map laurentResidue.toMonoidHom infinitesimalLoop = 1 := by
    apply Units.ext
    change laurentResidue (1 + nilpotentTerm) = 1
    rw [map_add, map_one]
    change 1 + (HahnSeries.single (-1 : ℤ) (DualNumber.eps : A)).map
      coefficientResidue.toZeroHom = 1
    rw [HahnSeries.map_single]
    change 1 + HahnSeries.single (-1 : ℤ) (0 : ℂ) = 1
    simp
  have hnotPositive : infinitesimalLoop ∉ positiveUnits := by
    rintro ⟨u, hu⟩
    have h := congrArg (fun w : (LaurentSeries A)ˣ ↦
      (w : LaurentSeries A).coeff (-1)) hu
    change ((u : PowerSeries A) : LaurentSeries A).coeff (-1) =
      (infinitesimalLoop : LaurentSeries A).coeff (-1) at h
    rw [PowerSeries.coeff_coe, ite_eq_left (show (-1 : ℤ) < 0 by decide), hcoeff] at h
    exact heps h.symm
  refine ⟨rfl, rfl, hcoeff, heps, hreduce, hnotPositive, ?_, ?_⟩
  · intro h
    have hmem := ((LatticeModels.cosetRelation positiveUnits) 1 infinitesimalLoop).mp h.symm
    exact hnotPositive (by simpa using hmem.1)
  · change coset complexPositiveUnits (Units.map laurentResidue.toMonoidHom infinitesimalLoop) =
      coset complexPositiveUnits 1
    rw [hreduce]

end

end RepTheorySurvey.Geometric.TorusDualNumbers
