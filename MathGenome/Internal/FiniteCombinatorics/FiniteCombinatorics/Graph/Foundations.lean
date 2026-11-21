import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations

universe u

noncomputable section

namespace FiniteCombinatorics.Graph

abbrev FiniteGraph : Specs.FiniteCombinatorics.Graph.Foundations.FiniteGraphType :=
  fun V _ => SimpleGraph V

abbrev edgeSubsets : Specs.FiniteCombinatorics.Graph.Foundations.edgeSubsetsType :=
  fun {_} _ _ G => Sym2.toFinset '' G.edgeSet

abbrev Subgraph : Specs.FiniteCombinatorics.Graph.Foundations.SubgraphType :=
  fun {_} _ G => G.Subgraph

abbrev induced : Specs.FiniteCombinatorics.Graph.Foundations.inducedType :=
  fun {_} _ G s => G.induce s

abbrev degree : Specs.FiniteCombinatorics.Graph.Foundations.degreeType :=
  fun {_} _ G v => Nat.card (G.neighborSet v)

abbrev WalkOfLength : Specs.FiniteCombinatorics.Graph.Foundations.WalkOfLengthType :=
  fun {_} _ G a b k => {p : G.Walk a b // p.length = k}

abbrev Path : Specs.FiniteCombinatorics.Graph.Foundations.PathType :=
  fun {_} _ G a b => G.Path a b

abbrev Cycle : Specs.FiniteCombinatorics.Graph.Foundations.CycleType :=
  fun {_} _ G a => {p : G.Walk a a // p.IsCycle}

abbrev Forest : Specs.FiniteCombinatorics.Graph.Foundations.ForestType :=
  fun {_} _ G => G.IsAcyclic

abbrev Tree : Specs.FiniteCombinatorics.Graph.Foundations.TreeType :=
  fun {_} _ G => G.IsTree

abbrev Component : Specs.FiniteCombinatorics.Graph.Foundations.ComponentType :=
  fun {_} _ G => G.ConnectedComponent

abbrev componentCount : Specs.FiniteCombinatorics.Graph.Foundations.componentCountType :=
  fun {_} _ G => Nat.card G.ConnectedComponent

theorem edge_subsets_iff : Specs.FiniteCombinatorics.Graph.Foundations.edge_subsets_iffType := by
  intro V _ _ G s
  constructor
  · rintro ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, b, he, Sym2.toFinset_mk_eq⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨s(a, b), hab, Sym2.toFinset_mk_eq⟩

theorem edge_subsets_card : Specs.FiniteCombinatorics.Graph.Foundations.edge_subsets_cardType := by
  intro V _ _ G s hs
  obtain ⟨e, he, rfl⟩ := hs
  exact Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet he)

theorem edge_membership : Specs.FiniteCombinatorics.Graph.Foundations.edge_membershipType := by intro V _ G a b; rfl

theorem subgraph_interface : Specs.FiniteCombinatorics.Graph.Foundations.subgraph_interfaceType := by
  intro V _ G H a b hab
  exact ⟨H.adj_sub hab, H.edge_vert hab, H.edge_vert hab.symm⟩

theorem induced_adjacency : Specs.FiniteCombinatorics.Graph.Foundations.induced_adjacencyType := by intro V _ G s a b; rfl

theorem degree_mathlib : Specs.FiniteCombinatorics.Graph.Foundations.degree_mathlibType := by
  intro V _ G v _
  exact (Nat.card_eq_fintype_card (α := G.neighborSet v)).trans
    (G.card_neighborSet_eq_degree v)

theorem walk_support : Specs.FiniteCombinatorics.Graph.Foundations.walk_supportType := by
  intro V _ G a b p
  exact ⟨p.length_support, p.isChain_adj_support⟩

theorem walk_endpoints : Specs.FiniteCombinatorics.Graph.Foundations.walk_endpointsType := by intro V _ G a b p; exact ⟨p.head_support, p.getLast_support⟩

theorem walk_from_sequence : Specs.FiniteCombinatorics.Graph.Foundations.walk_from_sequenceType := by
  intro V _ G l hne h
  exact ⟨.ofSupport l hne h, SimpleGraph.Walk.support_ofSupport hne h,
    SimpleGraph.Walk.length_ofSupport hne h⟩

theorem path_iff : Specs.FiniteCombinatorics.Graph.Foundations.path_iffType := by intro V _ G a b p; exact p.isPath_def

theorem cycle_iff : Specs.FiniteCombinatorics.Graph.Foundations.cycle_iffType := by
  intro V _ G a p
  by_cases hp : p.Nil
  · obtain rfl := hp.eq_nil
    simp [SimpleGraph.Walk.isCycle_def]
  · rw [SimpleGraph.Walk.isCycle_iff_isPath_dropLast_and_le_length,
      SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_dropLast hp, and_comm]

theorem reachability_equivalence : Specs.FiniteCombinatorics.Graph.Foundations.reachability_equivalenceType := by intro V _ G; exact G.reachable_is_equivalence

theorem walk_to_path : Specs.FiniteCombinatorics.Graph.Foundations.walk_to_pathType := by
  intro V _ G a b p
  classical
  exact ⟨p.bypass, p.bypass_isPath, p.length_bypass_le_length,
    p.support_bypass_sublist_support⟩

theorem reachable_iff_path : Specs.FiniteCombinatorics.Graph.Foundations.reachable_iff_pathType := by
  intro V _ G a b
  constructor
  · intro h
    exact h.elim_path fun p => ⟨p⟩
  · rintro ⟨p⟩
    exact p.val.reachable

theorem component_eq_iff : Specs.FiniteCombinatorics.Graph.Foundations.component_eq_iffType := by intro V _ G a b; exact SimpleGraph.ConnectedComponent.eq

theorem connected_iff_paths : Specs.FiniteCombinatorics.Graph.Foundations.connected_iff_pathsType := by
  intro V _ G
  constructor
  · intro h
    exact ⟨h.nonempty, fun a b => (reachable_iff_path G a b).mp (h a b)⟩
  · rintro ⟨hne, h⟩
    exact { preconnected := fun a b => (reachable_iff_path G a b).mpr (h a b), nonempty := hne }

theorem connected_iff_one_component : Specs.FiniteCombinatorics.Graph.Foundations.connected_iff_one_componentType := by
  intro V _ G
  change G.Connected ↔ Nat.card G.ConnectedComponent = 1
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · intro h
    haveI := h.nonempty
    exact ⟨h.preconnected.subsingleton_connectedComponent, inferInstance⟩
  · rintro ⟨hs, hn⟩
    haveI := hs
    obtain ⟨c⟩ := hn
    obtain ⟨v, hv⟩ := Quot.exists_rep c
    exact { preconnected := fun a b => SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _), nonempty := ⟨v⟩ }

theorem empty_components : Specs.FiniteCombinatorics.Graph.Foundations.empty_componentsType := by intro V _ _ G; exact Nat.card_of_isEmpty

theorem empty_no_walk : Specs.FiniteCombinatorics.Graph.Foundations.empty_no_walkType := by intro V _ _ G; rintro ⟨a, _, _⟩; exact isEmptyElim a

theorem empty_not_connected : Specs.FiniteCombinatorics.Graph.Foundations.empty_not_connectedType := by intro V _ _ G h; exact not_nonempty_iff.mpr inferInstance h.nonempty

theorem zero_length_path : Specs.FiniteCombinatorics.Graph.Foundations.zero_length_pathType := by intro V _ G a; exact ⟨SimpleGraph.Walk.IsPath.nil, rfl⟩

theorem forest_iff_no_cycle : Specs.FiniteCombinatorics.Graph.Foundations.forest_iff_no_cycleType := by intro V _ G; rfl

theorem tree_iff : Specs.FiniteCombinatorics.Graph.Foundations.tree_iffType := by intro V _ G; exact ⟨fun h => ⟨h.connected, h.isAcyclic⟩, fun h => ⟨h.1, h.2⟩⟩

end FiniteCombinatorics.Graph
