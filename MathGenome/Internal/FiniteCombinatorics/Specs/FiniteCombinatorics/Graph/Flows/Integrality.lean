import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations

/-! W48, integrality assertion. The indexed original arcs, real feasibility,
signed value, and cuts are those of W44. Capacities need only be natural
numbers embedded in the reals; no nonemptiness or simplicity is assumed. -/

universe u v
namespace FiniteCombinatorics.Graph.Flows.IntegralitySpec

/-- An integral flow maximizes value among all feasible real flows, and its
value is the capacity of a minimum cut. Natural loads express both integrality
and nonnegativity, including on loops and on parallel/opposite original arcs. -/
def integral_max_flow_min_cut : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A),
    (∀ a, ∃ c : ℕ, N.capacity a = (c : ℝ)) →
    ∃ (f : A → ℕ) (S : Set V),
      Spec.feasible N (fun a => (f a : ℝ)) ∧ Spec.isCut N S ∧
      (∀ g : A → ℝ, Spec.feasible N g →
        Spec.value N g ≤ Spec.value N (fun a => (f a : ℝ))) ∧
      (∀ T : Set V, Spec.isCut N T → Spec.cutCapacity N S ≤ Spec.cutCapacity N T) ∧
      Spec.value N (fun a => (f a : ℝ)) = Spec.cutCapacity N S

end FiniteCombinatorics.Graph.Flows.IntegralitySpec
