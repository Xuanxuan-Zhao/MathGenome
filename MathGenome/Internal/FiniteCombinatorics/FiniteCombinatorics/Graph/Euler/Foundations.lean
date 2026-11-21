import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Euler.Foundations

/-! The finite simple graph trail, Euler trail, edge support and Hamilton cycle
conventions of paper.tex, immediately before W39. -/

universe u
noncomputable section
namespace FiniteCombinatorics.Graph

abbrev IsTrail : Specs.FiniteCombinatorics.Graph.Euler.Foundations.IsTrailType :=
  fun {_} _ _ {_ _} p => p.IsTrail

abbrev IsEulerTrail : Specs.FiniteCombinatorics.Graph.Euler.Foundations.IsEulerTrailType :=
  fun {_} _ G {_ _} p => IsTrail G p ∧ ∀ e, e ∈ G.edgeSet → e ∈ p.edges

/-- Closed includes the walk with no edges at any vertex. -/
abbrev IsClosed : Specs.FiniteCombinatorics.Graph.Euler.Foundations.IsClosedType :=
  fun {_} _ _ {a b} _ => a = b

abbrev IsOpen : Specs.FiniteCombinatorics.Graph.Euler.Foundations.IsOpenType :=
  fun {_} _ _ {a b} _ => a ≠ b

abbrev edgeSupportVertices :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.edgeSupportVerticesType :=
  fun {_} _ G => {v | 0 < degree G v}

abbrev edgeSupport : Specs.FiniteCombinatorics.Graph.Euler.Foundations.edgeSupportType :=
  fun {_} _ G => G.induce (edgeSupportVertices G)

abbrev IsHamiltonCycle :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.IsHamiltonCycleType :=
  fun {_} _ _ {_} p => p.IsCycle ∧ ∀ v, v ∈ p.support

abbrev HamiltonCycle : Specs.FiniteCombinatorics.Graph.Euler.Foundations.HamiltonCycleType :=
  fun {_} _ G a => {p : G.Walk a a // IsHamiltonCycle G p}

theorem trail_iff : Specs.FiniteCombinatorics.Graph.Euler.Foundations.trail_iffType := by
  intro V _ G a b p
  exact p.isTrail_def

theorem eulerTrail_mathlib :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.eulerTrail_mathlibType := by
  intro V _ _ G a b p
  exact p.isEulerian_iff.symm

theorem eulerTrail_iff : Specs.FiniteCombinatorics.Graph.Euler.Foundations.eulerTrail_iffType := by
  intro V _ _ G a b p
  exact eulerTrail_mathlib G p

theorem eulerTrail_edgeSet :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.eulerTrail_edgeSetType := by
  intro V _ G a b p
  classical
  constructor
  · intro hp
    exact ⟨hp.1, ((eulerTrail_mathlib G p).mp hp).edgeSet_eq⟩
  · rintro ⟨hp, he⟩
    exact (eulerTrail_mathlib G p).mpr (hp.isEulerian_iff.mpr he)

theorem closed_iff : Specs.FiniteCombinatorics.Graph.Euler.Foundations.closed_iffType := by
  intro V _ G a b p
  rfl

theorem open_iff : Specs.FiniteCombinatorics.Graph.Euler.Foundations.open_iffType := by
  intro V _ G a b p
  rfl

theorem edgeSupportVertices_iff :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.edgeSupportVertices_iffType := by
  intro V _ G v
  rfl

theorem edgeSupportVertices_iff_exists_adj :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.edgeSupportVertices_iff_exists_adjType := by
  intro V _ G v
  classical
  let : Fintype V := Fintype.ofFinite V
  change 0 < Nat.card (G.neighborSet v) ↔ _
  rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
  exact G.degree_pos_iff_exists_adj v

theorem edgeSupport_adjacency :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.edgeSupport_adjacencyType := by
  intro V _ G a b
  rfl

theorem hamiltonCycle_iff :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.hamiltonCycle_iffType := by
  intro V _ G a p
  change (p.IsCycle ∧ ∀ v, v ∈ p.support) ↔ _
  rw [cycle_iff G a p, and_assoc]

theorem hamiltonCycle_mathlib :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.hamiltonCycle_mathlibType := by
  intro V _ _ G a p
  exact SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_forall_mem_support.symm

theorem nil_closed_eulerTrail :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.nil_closed_eulerTrailType := by
  intro V _ G h a
  refine ⟨⟨SimpleGraph.Walk.IsTrail.nil, ?_⟩, rfl⟩
  intro e he
  rw [h] at he
  exact False.elim he

theorem zero_length_closed_eulerTrail :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.zero_length_closed_eulerTrailType := by
  intro V _ G h a b p hp
  have hab := SimpleGraph.Walk.eq_of_length_eq_zero hp
  subst b
  have hnil := (SimpleGraph.Walk.length_eq_zero_iff.mp hp).eq_nil
  subst p
  exact nil_closed_eulerTrail G h a

theorem exists_closed_eulerTrail_of_no_edges :
    Specs.FiniteCombinatorics.Graph.Euler.Foundations.exists_closed_eulerTrail_of_no_edgesType := by
  intro V _ hn G h
  obtain ⟨a⟩ := hn
  exact ⟨a, .nil, (nil_closed_eulerTrail G h a).1, (nil_closed_eulerTrail G h a).2, rfl⟩

theorem empty_vertex_no_walk : Specs.FiniteCombinatorics.Graph.Euler.Foundations.empty_no_walkType := by
  exact FiniteCombinatorics.Graph.empty_no_walk

end FiniteCombinatorics.Graph
