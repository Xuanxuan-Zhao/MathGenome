import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.RestrictionSystem

/-! # Surjective restriction and composition
Proposition F07 of notes/003/advanced-field-theory.tex.
The normal restriction maps below apply without any finiteness hypothesis.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Restriction from the ambient automorphism group to a Galois intermediate field. -/
def restriction (M : IntermediateField K L) [IsGalois K M] :
    GaloisGroup K L →* stageGroup M :=
  AlgEquiv.restrictNormalHom M

/-- Restriction between Galois intermediate fields, using their literal inclusion. -/
def stageRestriction {E F : IntermediateField K L} (h : E ≤ F)
    [IsGalois K E] [IsGalois K F] : stageGroup F →* stageGroup E :=
  letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  AlgEquiv.restrictNormalHom E

@[simp] theorem restriction_apply (M : IntermediateField K L) [IsGalois K M]
    (σ : GaloisGroup K L) (x : M) :
    (restriction M σ x : L) = σ (x : L) :=
  AlgEquiv.restrictNormalHom_apply M σ x

theorem restriction_surjective [IsGalois K L]
    (M : IntermediateField K L) [IsGalois K M] :
    Function.Surjective (restriction M) :=
  AlgEquiv.restrictNormalHom_surjective L

theorem restriction_ker (M : IntermediateField K L) [IsGalois K M] :
    (restriction M).ker = fixingSubgroup M :=
  M.restrictNormalHom_ker

@[simp] theorem stageRestriction_apply {E F : IntermediateField K L} (h : E ≤ F)
    [IsGalois K E] [IsGalois K F] (σ : stageGroup F) (x : E) :
    (stageRestriction h σ x : L) = (σ (IntermediateField.inclusion h x) : L) := by
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact congrArg (fun y : F => (y : L)) (AlgEquiv.restrictNormal_commutes σ E x)

theorem stageRestriction_surjective {E F : IntermediateField K L} (h : E ≤ F)
    [IsGalois K E] [IsGalois K F] :
    Function.Surjective (stageRestriction h) := by
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom_surjective F

theorem stageRestriction_self (E : IntermediateField K L) [IsGalois K E] :
    stageRestriction (le_refl E) = MonoidHom.id (stageGroup E) := by
  ext σ x
  simp

theorem restriction_comp {E F : IntermediateField K L} (h : E ≤ F)
    [IsGalois K E] [IsGalois K F] :
    restriction E = (stageRestriction h).comp (restriction F) := by
  ext σ x
  simp only [MonoidHom.comp_apply, restriction_apply, stageRestriction_apply,
    IntermediateField.coe_inclusion]

theorem stageRestriction_comp {E F H : IntermediateField K L} (hEF : E ≤ F) (hFH : F ≤ H)
    [IsGalois K E] [IsGalois K F] [IsGalois K H] :
    stageRestriction (hEF.trans hFH) = (stageRestriction hEF).comp (stageRestriction hFH) := by
  ext σ x
  simp only [MonoidHom.comp_apply, stageRestriction_apply,
    IntermediateField.inclusion_inclusion]

end AdvancedFieldTheory
