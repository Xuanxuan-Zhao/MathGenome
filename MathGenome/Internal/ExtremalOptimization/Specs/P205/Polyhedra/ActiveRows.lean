import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Matrix.Basic

/-! Shared ordinary inequality-polyhedron interface for W32 (first conclusion).
Rows are covectors on the full coordinate space, including dimension zero. -/
namespace P205.Polyhedra

abbrev Coordinate (n : ℕ) := Fin n → ℝ

/-- The covector given by row `i` of `A`. -/
def rowCovector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Module.Dual ℝ (Coordinate n) where
  toFun x := ∑ j, A i j * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

/-- The ordinary polyhedron `Ax ≤ b`. -/
def polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set (Coordinate n) := {x | ∀ i, rowCovector A i x ≤ b i}

def activeRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Coordinate n) : Set (Fin m) := {i | rowCovector A i x = b i}

def activeSpan {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Coordinate n) : Submodule ℝ (Module.Dual ℝ (Coordinate n)) :=
  Submodule.span ℝ (rowCovector A '' activeRows A b x)

/-- Vertex uses Mathlib's standard open-segment definition of an extreme point. -/
def IsVertex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Coordinate n) : Prop := x ∈ (polyhedron A b).extremePoints ℝ

/-- The paper's midpoint test, with membership included. -/
def MidpointExtreme {n : ℕ} (P : Set (Coordinate n)) (x : Coordinate n) : Prop :=
  x ∈ P ∧ ∀ y ∈ P, ∀ z ∈ P, (1 / 2 : ℝ) • (y + z) = x → y = z

/-- Pointed means that no affine line with a nonzero direction is contained in `P`. -/
def IsPointed {n : ℕ} (P : Set (Coordinate n)) : Prop :=
  ¬ ∃ x d, d ≠ 0 ∧ ∀ t : ℝ, x + t • d ∈ P

namespace Expected

def convexPolyhedron : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), Convex ℝ (polyhedron A b)

def midpointIffVertex : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Coordinate n),
    MidpointExtreme (polyhedron A b) x ↔ IsVertex A b x

def vertexIffActiveSpan : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Coordinate n),
    x ∈ polyhedron A b → (IsVertex A b x ↔ activeSpan A b x = ⊤)

end Expected
end P205.Polyhedra
