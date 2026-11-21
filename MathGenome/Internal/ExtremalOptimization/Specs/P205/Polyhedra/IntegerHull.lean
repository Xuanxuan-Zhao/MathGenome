import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.IntegralVertices
import Mathlib.Analysis.Convex.Hull

/-! The full integer-hull clause of `paper.tex`, Theorem `p205:integer-hull`.
The lattice is represented by coordinatewise integer casts, and the hull is
ordinary convex hull, without closure or any feasibility/boundedness assumption. -/

namespace P205.Polyhedra.IntegerHullSpecs

def integer_hull : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ),
    A.IsTotallyUnimodular →
    polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) =
      convexHull ℝ {x | x ∈ polyhedron (A.map (Int.cast : ℤ → ℝ))
        (fun i => (b i : ℝ)) ∧ IsIntegralPoint x}

end P205.Polyhedra.IntegerHullSpecs
