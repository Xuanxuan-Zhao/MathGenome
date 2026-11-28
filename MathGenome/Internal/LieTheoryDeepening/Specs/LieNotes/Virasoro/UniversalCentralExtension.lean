import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.WittCohomology
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VirasoroStructure

/-! The universal property and the complete statement of Theorem KM11. -/

namespace LieNotes.Virasoro.VirasoroSpec

universe u v

/-- The canonical projection has central kernel. -/
def ProjectionCentralKernel : Prop :=
  ∀ x y : Vir, ProjectionOnCoordinates y = 0 → bracket x y = 0

/-- Every surjection onto Witt with central kernel receives a unique lift from Virasoro.
The lift is a linear map preserving the specified Virasoro bracket and commuting
with the canonical projection. -/
def UniversalProperty : Prop :=
  ∀ {E : Type u} [LieRing E] [LieAlgebra ℂ E] (p : E →ₗ⁅ℂ⁆ WittSpec.Witt),
    Function.Surjective p →
    (∀ x y : E, p y = 0 → ⁅x, y⁆ = 0) →
    ∃! f : Vir →ₗ[ℂ] E,
      p.toLinearMap.comp f = ProjectionOnCoordinates ∧
      ∀ x y : Vir, f (bracket x y) = ⁅f x, f y⁆

/-- The Virasoro cocycle classification and the canonical universal central extension. -/
def TheoremKM11 : Prop :=
  FormOnModes.{v} ∧ BundledCocycleExists.{v} ∧ WittCohomologySpec.Classification.{v} ∧
  WittCohomologySpec.ScalarCohomologyDimension ∧ ModeBracket ∧ CentralBracket ∧
  Center ∧ Perfectness ∧ CanonicalLieProjection ∧ ProjectionSurjective ∧
  ProjectionCentralKernel ∧ UniversalProperty.{u}

end LieNotes.Virasoro.VirasoroSpec
