import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Lattice.Fold

namespace Specs.P205

/-- Lemma 9.2 (`p205:matroid-support`). The maximum is the finite, nonempty
maximum `Finset.sup'`; the conclusion uses the ordinary convex hull. -/
def FiniteHullSupport : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F : Finset E) (hF : F.Nonempty) (x : E),
    (∀ w : E, inner ℝ w x ≤ F.sup' hF (fun z => inner ℝ w z)) →
    x ∈ convexHull ℝ (F : Set E)

end Specs.P205
