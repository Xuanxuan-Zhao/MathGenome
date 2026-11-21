import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! The three-dimensional ellipsoid lemma, `fa2:p2:ellipsoid`.
The inner product in ProjectionBody is only auxiliary. The conclusion supplies
an independently constructed positive definite quadratic form for the body. -/
namespace Specs.ExpandedFA.HilbertCharacterization.Ellipsoid
universe u
open Set ConvexBodySetup

/-- A nondegenerate ellipsoid centered at the prescribed center zero. -/
def IsEllipsoid {V : Type u} [AddCommGroup V] [Module ℝ V] (K : Set V) : Prop :=
  ∃ Q : QuadraticForm ℝ V, Q.PosDef ∧ K = {x | Q x ≤ 1}

/-- No smoothness, strict convexity, or preassigned gauge inner product is assumed. -/
def statement : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (K : Set V), ProjectionBody K → IsEllipsoid K

end Specs.ExpandedFA.HilbertCharacterization.Ellipsoid
