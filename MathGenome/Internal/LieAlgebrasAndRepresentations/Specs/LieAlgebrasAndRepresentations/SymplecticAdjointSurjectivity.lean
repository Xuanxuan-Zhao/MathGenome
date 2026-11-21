import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical

/-!
Matrix realization of the complex adjoint group used in LA-J07, lines 5057–5059.
This uses the diagonal-coordinate model of LA-D08 and the inner subgroup of
LA-J01. Semisimplicity is supplied independently in the application to real
forms.
-/

namespace Specs.LieAlgebrasAndRepresentations.SymplecticAdjointSurjectivity

open ClassicalRootsC Matrix

/-- Every complex automorphism of the specified symplectic matrix algebra is
conjugation by a complex symplectic matrix. -/
def adjointSurjectivityType : Prop :=
  ∀ n : ℕ, 0 < n → SolvableRadical.IsSemisimple_value ℂ (sp n) →
    ∀ g : sp n ≃ₗ⁅ℂ⁆ sp n, ∃ A : symplecticGroup (Fin n) ℂ,
      ∀ X : sp n,
        (g X : Mat n) = (A : Mat n) * (X : Mat n) *
          ((A⁻¹ : symplecticGroup (Fin n) ℂ) : Mat n)

end Specs.LieAlgebrasAndRepresentations.SymplecticAdjointSurjectivity
