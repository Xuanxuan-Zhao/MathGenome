import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.Category
import Mathlib.RingTheory.FiniteLength

/-! Finite length of the ordinary Verma module in the finite category O setup. -/

namespace Specs.RepTheorySurvey.CategoryO

open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open scoped ModuleCat.Algebra

universe u

/-- For each complex Cartan weight, the Verma module has finite length over the
universal enveloping algebra, with its canonical left action. -/
def verma_finite_length_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (lam : D.Weight), IsFiniteLength (U g) (verma_value D lam)

end Specs.RepTheorySurvey.CategoryO
