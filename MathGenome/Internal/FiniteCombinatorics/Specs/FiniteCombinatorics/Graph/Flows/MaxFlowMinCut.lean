import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations

/-! Independent statement of `paper.tex`, W46. Capacities are arbitrary
nonnegative real numbers on a finite type of original arcs. No nonemptiness,
loop-freeness, or restrictions on parallel or opposite arcs are imposed.
The value is signed source divergence, as in W44. -/

universe u v
namespace FiniteCombinatorics.Graph.Flows.Spec

/-- There are a feasible maximum flow and a minimum s–t cut with equal values.
Both optimization conclusions quantify over all feasible flows and all cuts. -/
def max_flow_min_cut : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A),
    ∃ (f : A → ℝ) (S : Set V),
      feasible N f ∧ isCut N S ∧
      (∀ g : A → ℝ, feasible N g → value N g ≤ value N f) ∧
      (∀ T : Set V, isCut N T → cutCapacity N S ≤ cutCapacity N T) ∧
      value N f = cutCapacity N S

end FiniteCombinatorics.Graph.Flows.Spec
