import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.IntegralVertices

/-! Independent specification of Theorem 7.5 (Hoffman–Kruskal).
The feasible set includes nonnegativity explicitly. No feasibility or boundedness
hypothesis is imposed on any right-hand side. -/
noncomputable section
namespace P205.Polyhedra

/-- The ordinary nonnegative inequality polyhedron for integer data. -/
def nonnegativePolyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) : Set (Coordinate n) :=
  {x | (∀ j, 0 ≤ x j) ∧ x ∈ polyhedron (A.map (Int.cast : ℤ → ℝ))
    (fun i => (b i : ℝ))}

namespace HoffmanKruskalSpecs

/-- Total unimodularity is equivalent to integrality of every vertex for every
integer right-hand side, including empty and unbounded feasible sets. -/
def hoffman_kruskal : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ),
  A.IsTotallyUnimodular ↔ ∀ (b : Fin m → ℤ) (x : Coordinate n),
    x ∈ (nonnegativePolyhedron A b).extremePoints ℝ → IsIntegralPoint x

end HoffmanKruskalSpecs
end P205.Polyhedra
