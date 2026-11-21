import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.ActiveRows
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.EReal.Basic

noncomputable section
open Matrix Set
namespace P205.Polyhedra

/-- The extended infimum includes both infinite values and the empty feasible set. -/
def objectiveInfimum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Coordinate n) : EReal :=
  sInf ((fun x : Coordinate n => ((c ⬝ᵥ x : ℝ) : EReal)) '' polyhedron A b)

def objectiveSupremum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Coordinate n) : EReal :=
  sSup ((fun x : Coordinate n => ((c ⬝ᵥ x : ℝ) : EReal)) '' polyhedron A b)

namespace VertexOptimumSpecs

def finite_infimum_vertex : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Coordinate n) (p : ℝ),
    (polyhedron A b).Nonempty → IsPointed (polyhedron A b) →
    objectiveInfimum A b c = (p : EReal) →
    ∃ x, IsVertex A b x ∧ c ⬝ᵥ x = p ∧
      ∀ y ∈ polyhedron A b, c ⬝ᵥ x ≤ c ⬝ᵥ y

def finite_supremum_vertex : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Coordinate n) (p : ℝ),
    (polyhedron A b).Nonempty → IsPointed (polyhedron A b) →
    objectiveSupremum A b c = (p : EReal) →
    ∃ x, IsVertex A b x ∧ c ⬝ᵥ x = p ∧
      ∀ y ∈ polyhedron A b, c ⬝ᵥ y ≤ c ⬝ᵥ x

end VertexOptimumSpecs
end P205.Polyhedra
