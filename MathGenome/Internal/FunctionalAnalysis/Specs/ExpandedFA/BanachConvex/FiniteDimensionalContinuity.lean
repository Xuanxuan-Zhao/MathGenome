import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent statement of paper.tex:8198–8208.
A finite function is represented by a real-valued function; only its values
on the open convex set matter. No lower semicontinuity, local boundedness,
nonemptiness, or positive-dimension assumption is imposed. -/

namespace ExpandedFA.BanachConvex.FiniteDimensionalContinuitySpec

/-- Every finite convex function on an open convex subset of real Euclidean
n-space is continuous on that subset, including n = 0 and the empty subset. -/
def FiniteConvexContinuity : Prop :=
  ∀ (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ),
    IsOpen U → ConvexOn ℝ U φ → ContinuousOn φ U

end ExpandedFA.BanachConvex.FiniteDimensionalContinuitySpec
