import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.MaxFlowMinCut
import MathGenome.Internal.ExtremalOptimization.P205.Networks.ResidualFoundation
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.MaxFlowMinCut
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Integrality

/-! Flow–cut optimality certificates (p205:W36).
The library real/integral existence results use exactly the canonical labelled
network. All cut sums below reduce to the shared bounded-network cut sums.
The residual certificate is transported in both directions on signed labels. -/

open scoped BigOperators Classical
universe u v
namespace P205.Networks
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows

/-- Reachability in the shared bounded residual graph with zero lower bounds. -/
def residualReachableSet := @FlowCutSpec.reachableSet

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- The cut conventions agree by definition, without discarding any arc labels. -/
theorem cutCapacity_eq_arcSum (N : Network V A) (S : Set V) :
    N.cutCapacity S = BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S) := rfl

theorem flow_cut_identity : FlowCutSpec.flow_cut_identity.{u,v} := by
  intro V A _ _ N f S hf hS
  exact N.value_eq_cut_net f S hf hS

theorem flow_cut_bound : FlowCutSpec.flow_cut_bound.{u,v} := by
  intro V A _ _ N f S hf hS
  exact N.weak_duality f S hf hS

theorem flow_cut_optimality : FlowCutSpec.flow_cut_optimality.{u,v} := by
  intro V A _ _ N f S hf hS heq
  constructor
  · exact ⟨hf, fun g hg => (flow_cut_bound N g S hg hS).trans_eq heq.symm⟩
  · intro T hT
    exact heq.symm.trans_le (flow_cut_bound N f T hf hT)

/-- Real attainment uses compactness, so no termination of real augmentation
and no integrality assumption enters the result. -/
theorem max_flow_min_cut : FlowCutSpec.max_flow_min_cut.{u,v} := by
  intro V A _ _ N
  exact N.max_flow_min_cut

/-- Convert nonnegative integer capacities to the natural witnesses required
by the library, and retain integer witnesses for every original arc load. -/
theorem integral_max_flow_min_cut : FlowCutSpec.integral_max_flow_min_cut.{u,v} := by
  intro V A _ _ N hc
  have hnat : ∀ a, ∃ n : ℕ, N.capacity a = (n : ℝ) := by
    intro a
    obtain ⟨z, hz⟩ := hc a
    have hnonneg : (0 : ℤ) ≤ z := by exact_mod_cast (hz ▸ N.capacity_nonneg a)
    refine ⟨z.toNat, ?_⟩
    rw [hz]
    exact_mod_cast (Int.toNat_of_nonneg hnonneg).symm
  obtain ⟨g, S, hg, hS, hmax, hmin, heq⟩ := N.integral_max_flow_min_cut hnat
  exact ⟨fun a => (g a : ℝ), S, hg, hS, hmax, hmin, heq,
    fun a => ⟨(g a : ℤ), by simp⟩⟩

/-- Reverse the upstream zero-lower-bound walk bridge, retaining both endpoints. -/
def fromLibraryWalk (N : Network V A) (f : A → ℝ) {x y : V} :
    Walk (N.residualGraph f) x y →
    Walk (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f) x y
  | .nil x => .nil x
  | .cons a p => .cons ⟨BoundedSpec.fromLibrary N f a.val, a.property⟩
      (fromLibraryWalk N f p)

/-- Reachability agrees for the bounded and library residual copies. -/
theorem residual_walk_iff (N : Network V A) (f : A → ℝ) (x y : V) :
    Nonempty (Walk (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f) x y) ↔
      Nonempty (Walk (N.residualGraph f) x y) :=
  ⟨fun ⟨p⟩ => ⟨BoundedSpec.toLibraryWalk N f p⟩,
    fun ⟨p⟩ => ⟨fromLibraryWalk N f p⟩⟩

theorem residualReachableSet_eq_library (N : Network V A) (f : A → ℝ) :
    residualReachableSet N f = N.residualReachableSet f := by
  ext x
  exact residual_walk_iff N f N.source x

/-- Absence of a walk yields the actual reachable-cut certificate used at
termination of augmentation; each outgoing/incoming original arc is exposed. -/
theorem residual_reachable_cut : FlowCutSpec.residual_reachable_cut.{u,v} := by
  intro V A _ _ N f hf hwalk
  have hw : ¬ Nonempty (Walk (N.residualGraph f) N.source N.sink) :=
    fun h => hwalk ((residual_walk_iff N f N.source N.sink).mpr h)
  obtain ⟨hS, hout, hin, heq⟩ := N.residual_reachable_cut f hf hw
  have hset : FlowCutSpec.reachableSet N f = N.residualReachableSet f :=
    residualReachableSet_eq_library N f
  rw [hset]
  have hv : N.value f = BoundedSpec.arcSum N.capacity
      (BoundedSpec.outgoing N.graph (N.residualReachableSet f)) := heq.symm
  obtain ⟨hmax, hmin⟩ := flow_cut_optimality N f _ hf hS hv
  exact ⟨hS, hout, hin, hv, hmax, hmin⟩

/-- Finite walk shortening makes the same certificate available when the
algorithm tests for a vertex-simple residual path. -/
theorem residual_reachable_cut_of_no_path :
    FlowCutSpec.residual_reachable_cut_of_no_path.{u,v} := by
  intro V A _ _ N f hf hpath
  apply residual_reachable_cut N f hf
  rintro ⟨p⟩
  obtain ⟨q, hq⟩ := Augmentation.exists_path p
  exact hpath ⟨⟨q, hq⟩⟩

end P205.Networks
