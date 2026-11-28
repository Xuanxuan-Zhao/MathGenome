import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.RankOneVermas
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ProjectiveCovers

/-! The principal component for the standard triangular decomposition of sl₂. -/

noncomputable section

open CategoryTheory
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)

namespace Specs.RepTheorySurvey.CategoryO.RankOnePrincipalComponent

open RankOneVermas (G IsStandard weight Verma Simple)
open ProjectiveCovers (IsIndecomposable componentObjects projectiveCover_value simpleIndex)
open ComponentBounds (centralCharacter_value inComponent_value simpleLabels_value)

/-- The joint index of the zero highest weight. -/
abbrev principalIndex (D : Setup G) := simpleIndex D (weight D 0)

/-- The central character at zero has exactly two scalar highest-weight parameters. -/
def CentralCharacterType : Prop :=
  ∀ (D : Setup G), IsStandard D → ∀ a : ℂ,
    centralCharacter_value D (weight D a) = centralCharacter_value D (weight D 0) ↔
      a = 0 ∨ a = -2

/-- Its two highest weights, with the zero and minus-two Cartan coordinates. -/
def SimpleLabelsType : Prop :=
  ∀ (D : Setup G), IsStandard D →
    simpleLabels_value D (principalIndex D) = {weight D 0, weight D (-2)}

/-- The zero cover is Verma, and the minus-two cover has the indicated
nonsplit short exact sequence of enveloping modules. -/
def CoverStructureType : Prop :=
  ∀ (D : Setup G), IsStandard D →
    (∀ (X : category_value.{0, 0} D) (p : X.obj →ₗ[U G] Simple D 0),
      projectiveCover_value X p → Nonempty (X.obj ≃ₗ[U G] Verma D 0)) ∧
    (∀ (X : category_value.{0, 0} D) (p : X.obj →ₗ[U G] Simple D (-2)),
      projectiveCover_value X p →
      ∃ (i : Verma D 0 →ₗ[U G] X.obj) (q : X.obj →ₗ[U G] Verma D (-2)),
        Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
        ¬ ∃ s : Verma D (-2) →ₗ[U G] X.obj, Function.RightInverse s q)

/-- For objects of the principal component, projectivity in the component
is equivalent to projectivity in the whole category. -/
def ProjectivityType : Prop :=
  ∀ (D : Setup G) (X : category_value.{0, 0} D)
    (hX : inComponent_value D X.obj (principalIndex D)),
    Projective (⟨X, hX⟩ : (componentObjects D (principalIndex D)).FullSubcategory) ↔
      Projective X

/-- Both indecomposable projective covers exist in the principal component,
and each indecomposable projective there is a cover of one of the two simples. -/
def IndecomposableProjectivesType : Prop :=
  ∀ (D : Setup G), IsStandard D →
    (∀ a : ℂ, (a = 0 ∨ a = -2) →
      ∃ (X : category_value.{0, 0} D) (p : X.obj →ₗ[U G] Simple D a),
        inComponent_value D X.obj (principalIndex D) ∧
        IsIndecomposable X.obj ∧ projectiveCover_value X p) ∧
    (∀ X : category_value.{0, 0} D,
      inComponent_value D X.obj (principalIndex D) → IsIndecomposable X.obj → Projective X →
      (∃ p : X.obj →ₗ[U G] Simple D 0, projectiveCover_value X p) ∨
      (∃ p : X.obj →ₗ[U G] Simple D (-2), projectiveCover_value X p))

end Specs.RepTheorySurvey.CategoryO.RankOnePrincipalComponent
