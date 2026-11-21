import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! The compact Killing form and semisimplicity needed for the symplectic
case of LA-J07, using the matrix model of LA-D08-C. -/

namespace Specs.LieAlgebrasAndRepresentations.SymplecticCompactKilling

open Matrix ClassicalRootsC
open LieAlgebrasAndRepresentations.RealForms

def compact_killing_type : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (ω : Conjugation (sp n)),
    (∀ X : sp n, (ω.map X : Mat n) = -X.valᴴ) →
    PolarRealStructures.IsCompact ω

def semisimple_type : Prop :=
  ∀ (n : ℕ), 0 < n → SolvableRadical.IsSemisimple_value ℂ (sp n)

end Specs.LieAlgebrasAndRepresentations.SymplecticCompactKilling
