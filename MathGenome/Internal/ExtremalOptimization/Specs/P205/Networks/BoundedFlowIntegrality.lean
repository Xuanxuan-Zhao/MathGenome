import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.IncidenceTU
import Mathlib.Analysis.Convex.Extreme

/-! The flow clauses of W35. Arc labels may include loops and parallel arcs.
There are no sign or ordering assumptions on the integer bounds. -/

universe u v
noncomputable section
open Matrix Set
namespace Specs.P205.Networks

/-- Flows with prescribed net outflow and finite integer coordinate bounds. -/
def boundedFlowSet {V : Type u} {E : Type v} [Fintype E]
    (tail head : E → V) (b : V → ℤ) (lower upper : E → ℤ) : Set (E → ℝ) :=
  {f | (directedIncidence tail head).map (Int.cast : ℤ → ℝ) *ᵥ f =
      (fun i => (b i : ℝ)) ∧
    ∀ e, (lower e : ℝ) ≤ f e ∧ f e ≤ (upper e : ℝ)}

namespace BoundedFlowIntegrality

/-- Every extreme point is integral, whether or not the feasible set is nonempty. -/
def vertex_integral : Prop :=
  ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (tail head : E → V) (b : V → ℤ) (lower upper : E → ℤ) (f : E → ℝ),
    f ∈ (boundedFlowSet tail head b lower upper).extremePoints ℝ →
    ∀ e, ∃ z : ℤ, f e = (z : ℝ)

/-- Any real arc objective has an integral minimizing vertex when feasible. -/
def integral_minimizer : Prop :=
  ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (tail head : E → V) (b : V → ℤ) (lower upper : E → ℤ) (c : E → ℝ),
    (boundedFlowSet tail head b lower upper).Nonempty →
    ∃ f, f ∈ (boundedFlowSet tail head b lower upper).extremePoints ℝ ∧
      (∀ e, ∃ z : ℤ, f e = (z : ℝ)) ∧
      ∀ g ∈ boundedFlowSet tail head b lower upper, c ⬝ᵥ f ≤ c ⬝ᵥ g

/-- Any real arc objective has an integral maximizing vertex when feasible. -/
def integral_maximizer : Prop :=
  ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (tail head : E → V) (b : V → ℤ) (lower upper : E → ℤ) (c : E → ℝ),
    (boundedFlowSet tail head b lower upper).Nonempty →
    ∃ f, f ∈ (boundedFlowSet tail head b lower upper).extremePoints ℝ ∧
      (∀ e, ∃ z : ℤ, f e = (z : ℝ)) ∧
      ∀ g ∈ boundedFlowSet tail head b lower upper, c ⬝ᵥ g ≤ c ⬝ᵥ f

end BoundedFlowIntegrality
end Specs.P205.Networks
