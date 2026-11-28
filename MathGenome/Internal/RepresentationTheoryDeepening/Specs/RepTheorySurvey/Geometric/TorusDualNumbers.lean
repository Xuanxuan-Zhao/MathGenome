import Mathlib.Algebra.DualNumber
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels

namespace RepTheorySurvey.Geometric.TorusDualNumberSpecs

noncomputable section

open LatticeModelSpecs (O K inclusion Grassmannian coset)

abbrev A := DualNumber ℂ

/-- The constant coefficient of a dual number. -/
def coefficientResidue : A →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

/-- Specialization on Laurent series applies the residue map to each coefficient. -/
def laurentResidue : LaurentSeries A →+* K where
  toFun f := f.map coefficientResidue
  map_one' := HahnSeries.map_one coefficientResidue.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul coefficientResidue.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero coefficientResidue.toZeroHom
  map_add' _ _ := HahnSeries.map_add coefficientResidue.toAddMonoidHom

abbrev positiveUnits : Subgroup (LaurentSeries A)ˣ :=
  (Units.map (HahnSeries.ofPowerSeries ℤ A).toMonoidHom).range

abbrev complexPositiveUnits : Subgroup Kˣ :=
  (Units.map inclusion.toMonoidHom).range

abbrev DualNumberGrassmannian := Grassmannian positiveUnits
abbrev ComplexGrassmannian := Grassmannian complexPositiveUnits

private theorem laurentResidue_ofPowerSeries (f : PowerSeries A) :
    laurentResidue (HahnSeries.ofPowerSeries ℤ A f) =
      inclusion (PowerSeries.map coefficientResidue f) := by
  apply HahnSeries.ext
  funext i
  change coefficientResidue ((f : LaurentSeries A).coeff i) =
    ((PowerSeries.map coefficientResidue f : O) : K).coeff i
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · rw [PowerSeries.coeff_map]

/-- Specialization on the rank-one loop quotient is induced by reduction modulo ε. -/
def specialize : DualNumberGrassmannian → ComplexGrassmannian :=
  Quotient.map (Units.map laurentResidue.toMonoidHom) (by
    intro g g' h
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    obtain ⟨u, hu⟩ := QuotientGroup.leftRel_apply.mp h
    rw [← hu]
    refine ⟨Units.map (PowerSeries.map coefficientResidue).toMonoidHom u, ?_⟩
    apply Units.ext
    exact (laurentResidue_ofPowerSeries (u : PowerSeries A)).symm)

/-- The Laurent monomial εt⁻¹. -/
def nilpotentTerm : LaurentSeries A := HahnSeries.single (-1 : ℤ) DualNumber.eps

/-- The loop 1 + εt⁻¹, with inverse 1 − εt⁻¹. -/
def infinitesimalLoop : (LaurentSeries A)ˣ := by
  have h₀ : nilpotentTerm * nilpotentTerm = 0 := by
    simp [nilpotentTerm, HahnSeries.single_mul_single]
  refine ⟨1 + nilpotentTerm, 1 - nilpotentTerm, ?_, ?_⟩
  · simp only [mul_sub, add_mul, mul_one, one_mul, h₀, add_zero, add_sub_cancel_right]
  · simp only [sub_mul, mul_add, mul_one, one_mul, h₀, sub_zero, sub_add_cancel]

namespace Expected

def specializeType := type_of% (@TorusDualNumberSpecs.specialize)

def infinitesimalLoopType := type_of% (@TorusDualNumberSpecs.infinitesimalLoop)

def ExampleProperties : Prop :=
  (infinitesimalLoop : LaurentSeries A) = 1 + HahnSeries.single (-1 : ℤ) DualNumber.eps ∧
  (↑(infinitesimalLoop⁻¹) : LaurentSeries A) = 1 - HahnSeries.single (-1 : ℤ) DualNumber.eps ∧
  (infinitesimalLoop : LaurentSeries A).coeff (-1) = DualNumber.eps ∧
  (DualNumber.eps : A) ≠ 0 ∧
  Units.map laurentResidue.toMonoidHom infinitesimalLoop = 1 ∧
  infinitesimalLoop ∉ positiveUnits ∧
  coset positiveUnits infinitesimalLoop ≠ coset positiveUnits 1 ∧
  specialize (coset positiveUnits infinitesimalLoop) = coset complexPositiveUnits 1

end Expected

end

end RepTheorySurvey.Geometric.TorusDualNumberSpecs
