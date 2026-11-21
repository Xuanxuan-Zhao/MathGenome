import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
Independent specification of F07, notes/003/advanced-field-theory.tex:308–344.
All fields are literal intermediate fields in the chosen ambient extension.
The transition map uses the algebra structure induced by literal inclusion.
There is no finite-degree hypothesis.
-/

universe u v

noncomputable section
set_option linter.checkUnivs false
namespace Specs.AdvancedFieldTheory

def restriction_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ (M : IntermediateField K L) [IsGalois K M], (L ≃ₐ[K] L) →* (M ≃ₐ[K] M)

def restriction_value : restriction_type :=
  fun {K} {L} [Field K] [Field L] [Algebra K L] M [IsGalois K M] => AlgEquiv.restrictNormalHom M

def stageRestriction_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ {E F : IntermediateField K L} (_h : E ≤ F) [IsGalois K E] [IsGalois K F],
    (F ≃ₐ[K] F) →* (E ≃ₐ[K] E)

def stageRestriction_value : stageRestriction_type :=
  fun {K} {L} [Field K] [Field L] [Algebra K L] {E F} h
    [IsGalois K E] [IsGalois K F] =>
    letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
    letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
    AlgEquiv.restrictNormalHom E

/-- Restriction acts on each element as the ambient automorphism. -/
def restriction_apply_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ (M : IntermediateField K L) [IsGalois K M] (σ : L ≃ₐ[K] L) (x : M),
    (restriction_value M σ x : L) = σ (x : L)

def restriction_surjective_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ [IsGalois K L] (M : IntermediateField K L) [IsGalois K M],
    Function.Surjective (restriction_value M)

def restriction_ker_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ (M : IntermediateField K L) [IsGalois K M],
    (restriction_value M).ker = M.fixingSubgroup

/-- Transition restriction is literal restriction along the inclusion E ⊆ F. -/
def stageRestriction_apply_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ {E F : IntermediateField K L} (h : E ≤ F) [IsGalois K E] [IsGalois K F]
    (σ : F ≃ₐ[K] F) (x : E),
    (stageRestriction_value h σ x : L) = (σ (IntermediateField.inclusion h x) : L)

def stageRestriction_surjective_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ {E F : IntermediateField K L} (h : E ≤ F) [IsGalois K E] [IsGalois K F],
    Function.Surjective (stageRestriction_value h)

def stageRestriction_self_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ (E : IntermediateField K L) [IsGalois K E],
    stageRestriction_value (le_refl E) = MonoidHom.id (E ≃ₐ[K] E)

def restriction_comp_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ {E F : IntermediateField K L} (h : E ≤ F) [IsGalois K E] [IsGalois K F],
    restriction_value E = (stageRestriction_value h).comp (restriction_value F)

def stageRestriction_comp_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
  ∀ {E F H : IntermediateField K L} (hEF : E ≤ F) (hFH : F ≤ H)
    [IsGalois K E] [IsGalois K F] [IsGalois K H],
    stageRestriction_value (hEF.trans hFH) =
      (stageRestriction_value hEF).comp (stageRestriction_value hFH)

end Specs.AdvancedFieldTheory
