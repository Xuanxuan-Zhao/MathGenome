import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.VertexOptimum
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.TotalUnimodularity
import Mathlib.Analysis.Normed.Group.Constructions

noncomputable section
open Matrix Set
namespace P205.Polyhedra

/-- Each coordinate is the real image of an integer. -/
def IsIntegralPoint {n : ℕ} (x : Coordinate n) : Prop :=
  ∀ j, ∃ z : ℤ, x j = (z : ℝ)

namespace IntegralVerticesSpecs

/-- The active square-system bridge, with no positivity assumptions. -/
def square_system_integral : Prop := ∀ {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (x : Coordinate n),
    (B.det = 1 ∨ B.det = -1) →
    (B.map (Int.cast : ℤ → ℝ)) *ᵥ x = (fun i => (b i : ℝ)) →
    IsIntegralPoint x

def vertex_integral : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (x : Coordinate n),
    A.IsTotallyUnimodular →
    IsVertex (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) x →
    IsIntegralPoint x

def finite_infimum_integral_vertex : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Coordinate n) (p : ℝ),
    A.IsTotallyUnimodular →
    (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty →
    IsPointed (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))) →
    objectiveInfimum (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) c = (p : EReal) →
    ∃ x, IsVertex (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) x ∧
      IsIntegralPoint x ∧ c ⬝ᵥ x = p ∧
      ∀ y ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)),
        c ⬝ᵥ x ≤ c ⬝ᵥ y

def finite_supremum_integral_vertex : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Coordinate n) (p : ℝ),
    A.IsTotallyUnimodular →
    (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty →
    IsPointed (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))) →
    objectiveSupremum (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) c = (p : EReal) →
    ∃ x, IsVertex (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) x ∧
      IsIntegralPoint x ∧ c ⬝ᵥ x = p ∧
      ∀ y ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)),
        c ⬝ᵥ y ≤ c ⬝ᵥ x

/-- Boundedness alone supplies finite attainment and pointedness. -/
def bounded_integral_minimizer : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Coordinate n),
    A.IsTotallyUnimodular →
    (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty →
    Bornology.IsBounded (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))) →
    ∃ x, IsVertex (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) x ∧
      IsIntegralPoint x ∧
      ∀ y ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)),
        c ⬝ᵥ x ≤ c ⬝ᵥ y

def bounded_integral_maximizer : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Coordinate n),
    A.IsTotallyUnimodular →
    (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty →
    Bornology.IsBounded (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))) →
    ∃ x, IsVertex (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) x ∧
      IsIntegralPoint x ∧
      ∀ y ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)),
        c ⬝ᵥ y ≤ c ⬝ᵥ x

end IntegralVerticesSpecs
end P205.Polyhedra
