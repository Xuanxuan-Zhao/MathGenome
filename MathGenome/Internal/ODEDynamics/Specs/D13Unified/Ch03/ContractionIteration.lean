import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Logic.Function.Iterate

/-!
Independent statements for paper.tex, Chapter 3, Lemma d13:03:contraction.
The ambient space is a complete normed additive group; this includes the
Banach spaces of the source without needing scalar multiplication.
The self-map has domain and codomain the closed subset, represented as a subtype.
-/

open Filter Function
open scoped Topology

universe u

namespace Specs.D13Unified.Ch03.ContractionIteration

/-- Existence, uniqueness, convergence from every starting point, and the
source's a priori estimate. The natural index includes zero and q may be zero. -/
def contractionIteration_type : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [CompleteSpace E]
    (X : Set E), X.Nonempty → IsClosed X →
    ∀ (K : X → X) (q : ℝ), 0 ≤ q → q < 1 →
    (∀ u v : X, ‖(K u : E) - (K v : E)‖ ≤ q * ‖(u : E) - (v : E)‖) →
    ∃ uStar : X, K uStar = uStar ∧
      (∀ v : X, K v = v → v = uStar) ∧
      ∀ u0 : X,
        Tendsto (fun j : ℕ => (K^[j] u0 : E)) atTop (𝓝 (uStar : E)) ∧
        ∀ j : ℕ, ‖(K^[j] u0 : E) - (uStar : E)‖ ≤
          q ^ j / (1 - q) * ‖(K u0 : E) - (u0 : E)‖

/-- The same conclusion for an arbitrary sequence satisfying the recurrence,
so no special choice of implementation of the iterates is imposed. -/
def contractionSequence_type : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [CompleteSpace E]
    (X : Set E), X.Nonempty → IsClosed X →
    ∀ (K : X → X) (q : ℝ), 0 ≤ q → q < 1 →
    (∀ u v : X, ‖(K u : E) - (K v : E)‖ ≤ q * ‖(u : E) - (v : E)‖) →
    ∃ uStar : X, K uStar = uStar ∧
      (∀ v : X, K v = v → v = uStar) ∧
      ∀ u : ℕ → X, (∀ j : ℕ, u (j + 1) = K (u j)) →
        Tendsto (fun j : ℕ => (u j : E)) atTop (𝓝 (uStar : E)) ∧
        ∀ j : ℕ, ‖(u j : E) - (uStar : E)‖ ≤
          q ^ j / (1 - q) * ‖(u 1 : E) - (u 0 : E)‖

end Specs.D13Unified.Ch03.ContractionIteration
