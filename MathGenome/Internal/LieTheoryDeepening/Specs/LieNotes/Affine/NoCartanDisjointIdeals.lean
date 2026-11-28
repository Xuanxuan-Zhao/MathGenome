import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.TriangularRootSpaces

namespace Specs.LieNotes.Affine.NoCartanDisjointIdeals

open _root_.RepTheorySurvey.Affine
open _root_.Specs.RepTheorySurvey.Affine.TriangularRootSpaces (affineCartan_value)

universe u

/-- Every nonzero ideal of the normalized untwisted affine Lie algebra meets
the affine Cartan subalgebra nontrivially. -/
def NonzeroIdealMeetsAffineCartan : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra], B.IsNormalized H →
    ∀ I : LieIdeal ℂ (AffineAlgebra B), I ≠ ⊥ →
      I.toSubmodule ⊓ affineCartan_value B H ≠ ⊥

end Specs.LieNotes.Affine.NoCartanDisjointIdeals
