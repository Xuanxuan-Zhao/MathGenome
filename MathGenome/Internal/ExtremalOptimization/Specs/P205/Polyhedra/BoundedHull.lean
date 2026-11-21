import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
The last assertion of `paper.tex`, Theorem `p205:W32` (lines 1516,
1544–1552). Vector inequalities are coordinatewise, and vertices mean
extreme points. `convexHull` is the ordinary hull of finite convex
combinations; no closure is taken. Both matrix dimensions may be zero.
-/

namespace P205.Polyhedra.Specs

/-- Every nonempty bounded finite real halfspace polyhedron is the ordinary
convex hull of its vertices. No full-dimensionality hypothesis is imposed. -/
def bounded_polyhedron_hull : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
    let P : Set (Fin n → ℝ) := {x | A.mulVec x ≤ b}
    P.Nonempty → Bornology.IsBounded P →
      P = convexHull ℝ (P.extremePoints ℝ)

end P205.Polyhedra.Specs
