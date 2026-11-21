import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Foundations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Powerset

/-! Independent statements for the counting, subset formula, uniqueness and boundary
cases of paper.tex W60. Edges are unordered pairs in `Sym2 V`, the same edge set
as in the shared graph foundations. `fromEdgeSet` keeps the entire vertex type,
so its connected components include every isolated vertex. -/

open scoped BigOperators
open Polynomial
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial

/-- All edges of a finite simple graph, each counted once. -/
def edges {V : Type u} [Finite V] (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact (Set.toFinite G.edgeSet).toFinset

/-- The spanning graph `(V,A)`, retaining isolated vertices. -/
def spanningGraph {V : Type u} (A : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (A : Set (Sym2 V))

def spanningComponentCount {V : Type u} (A : Finset (Sym2 V)) : ℕ :=
  Nat.card (spanningGraph A).ConnectedComponent

/-- The edge-subset polynomial with integer coefficients. -/
def chromaticPolynomial {V : Type u} [Finite V] (G : SimpleGraph V) : ℤ[X] := by
  classical
  exact ∑ A ∈ (edges G).powerset,
    C ((-1 : ℤ) ^ A.card) * X ^ spanningComponentCount A

def spanningComponentCountType := ∀ {V : Type u}, Finset (Sym2 V) → ℕ
abbrev spanningComponentCountValue : spanningComponentCountType := @spanningComponentCount

def chromaticPolynomialType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℤ[X]
abbrev chromaticPolynomialValue : chromaticPolynomialType := @chromaticPolynomial

def subsetFormula : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  chromaticPolynomial G = ∑ A ∈ (edges G).powerset,
    C ((-1 : ℤ) ^ A.card) * X ^ spanningComponentCount A

def countsColorings : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ),
  (chromaticPolynomial G).eval (k : ℤ) = (Nat.card (G.Coloring (Fin k)) : ℤ)

def uniquePolynomial : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  ∃! P : ℤ[X], ∀ k : ℕ, P.eval (k : ℤ) = (Nat.card (G.Coloring (Fin k)) : ℤ)

def edgelessPolynomial : Prop := ∀ {V : Type u} [Finite V],
  chromaticPolynomial (⊥ : SimpleGraph V) = X ^ Nat.card V

def emptyPolynomial : Prop := ∀ {V : Type u} [Finite V] [IsEmpty V] (G : SimpleGraph V),
  chromaticPolynomial G = 1

def emptyColoringCount : Prop := ∀ {V : Type u} [Finite V] [IsEmpty V]
  (G : SimpleGraph V) (k : ℕ), Nat.card (G.Coloring (Fin k)) = 1

end Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial
