import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.OrderedCechComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ProjectiveSpaces
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.ProjectiveFiniteness

open OrderedCechComparison (SchemeOverRing cohomology)

/-- Over a field, every cohomology group of a coherent module sheaf on a closed
subscheme of projective space is finite dimensional over the field. Locally
finite presentation is the coherence condition on these locally Noetherian schemes. -/
def ProjectiveCohomologyFiniteness : Prop :=
  ∀ (k W : Type u) [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    (X : SchemeOverRing k) (i : X ⟶ ProjectiveSpaces.projectiveSpace k W)
    [IsClosedImmersion i.left] (F : X.left.Modules) [F.IsFinitePresentation]
    (n : ℕ), FiniteDimensional k ((cohomology X n).obj F)

end LinearAlgebraicGroups.Specs.ProjectiveFiniteness
