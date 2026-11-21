import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.RealAttainment
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.ResidualOptimality
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.WeakDuality
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.MaxFlowMinCut

/-! Maximum flow and minimum cut for arbitrary finite real capacities (W46).
Compactness supplies a maximizing flow. Its positive-residual reachable set
is a cut of equal capacity; weak duality proves minimality among all cuts.
No termination of real-valued augmentation is assumed. -/

universe u v
namespace FiniteCombinatorics.Graph.Flows.Network

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- Every finite real network has a maximum flow and a minimum cut of equal
value, including networks with no arcs, zero capacities, or loops. -/
theorem max_flow_min_cut (N : Network V A) :
    ∃ (f : A → ℝ) (S : Set V),
      N.Feasible f ∧ N.IsCut S ∧
      (∀ g : A → ℝ, N.Feasible g → N.value g ≤ N.value f) ∧
      (∀ T : Set V, N.IsCut T → N.cutCapacity S ≤ N.cutCapacity T) ∧
      N.value f = N.cutCapacity S := by
  obtain ⟨f, hmax⟩ := N.exists_maximum
  have hwalk := (N.maximum_iff_no_residual_walk f hmax.1).mp hmax
  obtain ⟨hS, _, _, heq⟩ := N.residual_reachable_cut f hmax.1 hwalk
  refine ⟨f, N.residualReachableSet f, hmax.1, hS, hmax.2, ?_, heq.symm⟩
  intro T hT
  exact heq.trans_le (N.weak_duality f T hmax.1 hT)

end FiniteCombinatorics.Graph.Flows.Network
