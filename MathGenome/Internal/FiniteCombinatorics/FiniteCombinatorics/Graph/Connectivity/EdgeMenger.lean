import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Connectivity.EdgeMenger
import Mathlib.Data.Finset.Card
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Integrality
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.PathCycleDecomposition

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.EdgeMenger
variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- Every path meets any edge separator. -/
theorem path_meets_separator (p : G.Path s t) {F : Finset (Sym2 V)}
    (hF : Separator G s t F) : ∃ e ∈ F, e ∈ pathEdges p := by
  obtain ⟨e, he, hep⟩ := p.val.exists_mem_edges_of_not_reachable_deleteEdges hF.2
  exact ⟨e, he, by simpa [pathEdges] using hep⟩

/-- Disjoint sets meeting a fixed finite set are bounded in number by its size. -/
theorem packing_le_hitting_set (ps : List (G.Path s t)) (F : Finset (Sym2 V))
    (hp : Packing ps) (hh : ∀ p ∈ ps, ∃ e ∈ F, e ∈ pathEdges p) :
    ps.length ≤ F.card := by
  classical
  induction ps generalizing F with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hd, ht⟩ := List.pairwise_cons.mp hp
    obtain ⟨e, heF, hep⟩ := hh p (by simp)
    have hh' : ∀ q ∈ ps, ∃ a ∈ F.erase e, a ∈ pathEdges q := by
      intro q hq
      obtain ⟨a, haF, haq⟩ := hh q (by simp [hq])
      refine ⟨a, Finset.mem_erase.mpr ⟨?_, haF⟩, haq⟩
      intro hae
      subst a
      exact Finset.disjoint_left.mp (hd q hq) hep haq
    have hb := ih (F.erase e) ht hh'
    have hcard := Finset.card_erase_add_one heF
    simp only [List.length_cons]
    omega

/-- Choosing one separator edge from each path gives distinct edges. -/
theorem packing_le_separator : packing_le_separator_type.{u} := by
  intro V G s t ps F hp hF
  exact packing_le_hitting_set ps F hp (fun p _ => path_meets_separator p hF)

theorem disconnected : disconnected_type.{u} := by
  intro V _ G s t hst
  refine ⟨by simp [Packing], ⟨by simp, ?_⟩, ?_, ?_⟩
  · simpa using hst
  · intro ps _
    cases ps with
    | nil => rfl
    | cons p ps => exact (hst p.val.reachable).elim
  · intro F _
    exact Nat.zero_le _

section Network
open scoped Classical BigOperators
variable [Fintype V]

theorem boundary_subset (S : Set V) :
    (↑(boundary G S) : Set (Sym2 V)) ⊆ G.edgeSet := by
  intro e he
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
  exact a.edge_mem

theorem edge_mem_boundary (S : Set V) {x y : V} (hxy : G.Adj x y) :
    s(x, y) ∈ boundary G S ↔ (x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S) := by
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
    have ha' := (Finset.mem_filter.mp ha).2
    rcases SimpleGraph.dart_edge_eq_mk'_iff'.mp he with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact Or.inl ⟨hx ▸ ha'.1, hy ▸ ha'.2⟩
    · exact Or.inr ⟨hy ▸ ha'.1, hx ▸ ha'.2⟩
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · exact Finset.mem_image.mpr ⟨⟨(x, y), hxy⟩, by simp [hx, hy], rfl⟩
    · exact Finset.mem_image.mpr ⟨⟨(y, x), hxy.symm⟩, by simp [hx, hy], Sym2.eq_swap⟩

/-- Removing every crossing edge prevents leaving the source side. -/
theorem boundary_separates (S : Set V) (hs : s ∈ S) (ht : t ∉ S) :
    Separator G s t (boundary G S) := by
  refine ⟨boundary_subset S, ?_⟩
  rintro ⟨p⟩
  have stay {x y : V} (p : (G.deleteEdges (↑(boundary G S))).Walk x y) :
      x ∈ S → y ∈ S := by
    induction p with
    | nil => exact id
    | @cons x y z h p ih =>
      intro hx
      apply ih
      by_contra hy
      exact (SimpleGraph.deleteEdges_adj.mp h).2 ((edge_mem_boundary S (SimpleGraph.deleteEdges_adj.mp h).1).mpr (Or.inl ⟨hx, hy⟩))
  exact ht (stay p hs)

/-- The outgoing darts are in bijection with the crossing unordered edges. -/
theorem boundary_card_eq (s t : V) (hst : s ≠ t) (S : Set V) :
    ((boundary G S).card : ℝ) = Flows.Spec.cutCapacity (unitNetwork G s t hst) S := by
  have hinj : Set.InjOn (SimpleGraph.Dart.edge : G.Dart → Sym2 V)
      (↑(Finset.univ.filter (fun a : G.Dart => a.fst ∈ S ∧ a.snd ∉ S))) := by
    intro a ha b hb he
    rcases (SimpleGraph.dart_edge_eq_iff a b).mp he with h | h
    · exact h
    · have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      subst a
      exact (hb'.2 ha'.1).elim
  have hc := Finset.card_image_of_injOn hinj
  change ((Finset.image SimpleGraph.Dart.edge _).card : ℝ) = _
  rw [hc]
  change _ = ∑ a ∈ Finset.univ.filter (fun a : G.Dart => a.fst ∈ S ∧ a.snd ∉ S), (1 : ℝ)
  simp

/-- A separator contains the boundary of its source's component after deletion. -/
theorem reachable_boundary_subset {F : Finset (Sym2 V)} (hF : Separator G s t F) :
    boundary G {x | (G.deleteEdges (↑F : Set (Sym2 V))).Reachable s x} ⊆ F := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hx, hy⟩ := (Finset.mem_filter.mp ha).2
  by_contra hn
  apply hy
  exact hx.trans (SimpleGraph.Adj.reachable (show (G.deleteEdges (↑F : Set (Sym2 V))).Adj
    a.fst a.snd from SimpleGraph.deleteEdges_adj.mpr ⟨a.adj, hn⟩))

/-- Reversing all darts is an involutive reindexing of the finite arc set. -/
def reverseDarts (G : SimpleGraph V) : G.Dart ≃ G.Dart :=
  { toFun := SimpleGraph.Dart.symm
    invFun := SimpleGraph.Dart.symm
    left_inv := SimpleGraph.Dart.symm_symm
    right_inv := SimpleGraph.Dart.symm_symm }

/-- Divergence can be computed from the signed net load on each outgoing edge. -/
theorem dart_divergence (f : G.Dart → ℝ) (x : V) :
    Directed.Spec.divergence (dartGraph G) f x =
      ∑ a : G.Dart, if a.fst = x then f a - f a.symm else 0 := by
  have hs : (∑ a : G.Dart, if a.snd = x then f a else 0) =
      ∑ a : G.Dart, if a.fst = x then f a.symm else 0 := by
    apply Fintype.sum_equiv (reverseDarts G)
    intro a
    simp [reverseDarts]
  change (∑ a ∈ Finset.univ.filter (fun a : G.Dart => a.fst = x), f a) -
    (∑ a ∈ Finset.univ.filter (fun a : G.Dart => a.snd = x), f a) = _
  simp only [Finset.sum_filter]
  rw [hs, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

/-- Cancel simultaneous opposite integer loads. -/
def cancel (f : G.Dart → ℕ) (a : G.Dart) : ℕ := f a - f a.symm

theorem cancel_net (f : G.Dart → ℕ) (a : G.Dart) :
    ((cancel f a : ℕ) : ℝ) - ((cancel f a.symm : ℕ) : ℝ) =
      (f a : ℝ) - (f a.symm : ℝ) := by
  simp only [cancel, SimpleGraph.Dart.symm_symm]
  rcases le_total (f a) (f a.symm) with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, Nat.cast_sub h]
    ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, Nat.cast_sub h]
    ring

theorem cancel_divergence (f : G.Dart → ℕ) (x : V) :
    Directed.Spec.divergence (dartGraph G) (fun a => (cancel f a : ℝ)) x =
      Directed.Spec.divergence (dartGraph G) (fun a => (f a : ℝ)) x := by
  rw [dart_divergence, dart_divergence]
  apply Finset.sum_congr rfl
  intro a _
  simp only [cancel_net]

theorem cancel_le (f : G.Dart → ℕ) (a : G.Dart) : cancel f a ≤ f a := Nat.sub_le _ _

theorem cancel_opposite (f : G.Dart → ℕ) (a : G.Dart) :
    cancel f a = 0 ∨ cancel f a.symm = 0 := by
  simp only [cancel, SimpleGraph.Dart.symm_symm]
  omega

/-- Cancellation preserves feasibility and signed value in the unit network. -/
theorem cancel_feasible_value (s t : V) (hst : s ≠ t) (f : G.Dart → ℕ)
    (hf : Flows.Spec.feasible (unitNetwork G s t hst) (fun a => (f a : ℝ))) :
    Flows.Spec.feasible (unitNetwork G s t hst) (fun a => (cancel f a : ℝ)) ∧
      Flows.Spec.value (unitNetwork G s t hst) (fun a => (cancel f a : ℝ)) =
        Flows.Spec.value (unitNetwork G s t hst) (fun a => (f a : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, cancel_divergence f s⟩
  · intro a
    refine ⟨Nat.cast_nonneg _, ?_⟩
    exact (Nat.cast_le.mpr (cancel_le f a)).trans (hf.1 a).2
  · intro x hx ht
    change Directed.Spec.divergence (dartGraph G) (fun a => (cancel f a : ℝ)) x = 0
    rw [cancel_divergence]
    exact hf.2 x hx ht

/-- Forgetting dart orientations retains every endpoint and incidence. -/
def undirect {x y : V} : Directed.Walk (dartGraph G) x y → G.Walk x y
  | .nil _ => .nil
  | .cons a p => .cons (by
      have ht : a.val.fst = _ := a.property.1
      have hh : a.val.snd = _ := a.property.2
      exact (congrArg₂ G.Adj ht hh).mp a.val.adj) (undirect p)

@[simp] theorem undirect_support {x y : V} (p : Directed.Walk (dartGraph G) x y) :
    (undirect p).support = Directed.Spec.vertices p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [undirect, Directed.Spec.vertices, ih]

@[simp] theorem undirect_edges {x y : V} (p : Directed.Walk (dartGraph G) x y) :
    (undirect p).edges = (Directed.Spec.arcs p).map SimpleGraph.Dart.edge := by
  induction p with
  | nil => rfl
  | @cons x y z a p ih =>
    have ht : a.val.fst = x := a.property.1
    have hh : a.val.snd = y := a.property.2
    simp [undirect, Directed.Spec.arcs, ih, SimpleGraph.Dart.edge, ht, hh]

/-- Vertex simplicity is unchanged on forgetting orientations. -/
def undirectPath {x y : V} (p : Directed.Spec.path (dartGraph G) x y) : G.Path x y :=
  ⟨undirect p.val, (SimpleGraph.Walk.isPath_def _).mpr (by
    rw [undirect_support]
    exact p.property)⟩

theorem undirectPath_edges {x y : V} (p : Directed.Spec.path (dartGraph G) x y)
    (e : Sym2 V) :
    e ∈ pathEdges (undirectPath p) ↔
      ∃ a ∈ Directed.Spec.arcs p.val, a.edge = e := by
  simp [pathEdges, undirectPath, undirect_edges]

theorem path_has_arc (hst : s ≠ t) (p : Directed.Spec.path (dartGraph G) s t) :
    ∃ a, a ∈ Directed.Spec.arcs p.val := by
  rcases p with ⟨p, hp⟩
  cases p with
  | nil => exact (hst rfl).elim
  | cons a p => exact ⟨a.val, by simp [Directed.Spec.arcs]⟩

open Flows

private def pathLoad (ps : List (ℤ × Directed.Spec.path (dartGraph G) s t))
    (a : G.Dart) : ℤ :=
  (ps.map fun p => PathCycleSpec.pathContribution p.1 p.2 a).sum

private theorem contribution_nonneg (p : ℤ × Directed.Spec.path (dartGraph G) s t)
    (hp : 0 < p.1) (a : G.Dart) : 0 ≤ PathCycleSpec.pathContribution p.1 p.2 a := by
  unfold PathCycleSpec.pathContribution
  split_ifs <;> omega

private theorem pathLoad_nonneg (ps : List (ℤ × Directed.Spec.path (dartGraph G) s t))
    (hp : ∀ p ∈ ps, 0 < p.1) (a : G.Dart) : 0 ≤ pathLoad ps a := by
  apply List.sum_nonneg
  intro z hz
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hz
  exact contribution_nonneg p (hp p hpm) a

private theorem weight_le_pathLoad
    (ps : List (ℤ × Directed.Spec.path (dartGraph G) s t))
    (hp : ∀ p ∈ ps, 0 < p.1)
    (p : ℤ × Directed.Spec.path (dartGraph G) s t) (hpm : p ∈ ps)
    (a : G.Dart) (ha : a ∈ Directed.Spec.arcs p.2.val) : p.1 ≤ pathLoad ps a := by
  have hnonneg : ∀ z ∈ ps.map (fun p => PathCycleSpec.pathContribution p.1 p.2 a), 0 ≤ z := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact contribution_nonneg q (hp q hq) a
  simpa [pathLoad, PathCycleSpec.pathContribution, ha] using
    List.single_le_sum hnonneg _ (List.mem_map.mpr ⟨p, hpm, rfl⟩)

/-- An integral path family dominated by unit, nonopposite loads projects to
edge-disjoint undirected paths, each with coefficient one. -/
theorem packing_of_unit_load (hst : s ≠ t) (g : G.Dart → ℤ)
    (hunit : ∀ a, g a ≤ 1) (hop : ∀ a, g a = 0 ∨ g a.symm = 0)
    (ps : List (ℤ × Directed.Spec.path (dartGraph G) s t))
    (hp : ∀ p ∈ ps, 0 < p.1) (hb : ∀ a, pathLoad ps a ≤ g a) :
    Packing (ps.map fun p => undirectPath p.2) ∧
      (ps.map Prod.fst).sum = (ps.length : ℤ) := by
  induction ps with
  | nil => simp [Packing]
  | cons p ps ih =>
    have hpp : 0 < p.1 := hp p (by simp)
    have hpt : ∀ q ∈ ps, 0 < q.1 := fun q hq => hp q (by simp [hq])
    have hhead (a : G.Dart) :
        PathCycleSpec.pathContribution p.1 p.2 a + pathLoad ps a ≤ g a := by
      simpa [pathLoad] using hb a
    have hbt (a : G.Dart) : pathLoad ps a ≤ g a := by
      have hn := contribution_nonneg p hpp a
      linarith [hhead a]
    obtain ⟨hpack, hsum⟩ := ih hpt hbt
    have hpone : p.1 = 1 := by
      obtain ⟨a, ha⟩ := path_has_arc hst p.2
      have hd := hhead a
      simp only [PathCycleSpec.pathContribution, ite_eq_left ha] at hd
      have hn := pathLoad_nonneg ps hpt a
      have hu := hunit a
      omega
    refine ⟨?_, ?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_, hpack⟩
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      apply Finset.disjoint_left.mpr
      intro e hep her
      obtain ⟨a, ha, hae⟩ := (undirectPath_edges p.2 e).mp hep
      obtain ⟨b, hb', hbe⟩ := (undirectPath_edges r.2 e).mp her
      have hwa := hhead a
      simp only [PathCycleSpec.pathContribution, ite_eq_left ha] at hwa
      have hwb := weight_le_pathLoad ps hpt r hr b hb'
      have hrpos := hpt r hr
      rcases (SimpleGraph.dart_edge_eq_iff a b).mp (hae.trans hbe.symm) with hab | hab
      · subst b
        have hu := hunit a
        omega
      · have hga : 0 < g a := by
          have hn := pathLoad_nonneg ps hpt a
          omega
        have hgb : 0 < g b := lt_of_lt_of_le hrpos (hwb.trans (hbt b))
        rcases hop a with hz | hz
        · omega
        · have he : a.symm = b := by rw [hab, SimpleGraph.Dart.symm_symm]
          rw [he] at hz
          omega
    · simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [hpone, hsum]
      omega

/-- Integral max-flow/min-cut, followed by cancellation and decomposition,
produces an undirected packing and separator of exactly the same size. -/
theorem exists_equal_packing_separator (s t : V) (hst : s ≠ t) :
    ∃ (ps : List (G.Path s t)) (F : Finset (Sym2 V)),
      Packing ps ∧ Separator G s t F ∧ ps.length = F.card := by
  let N := unitNetwork G s t hst
  obtain ⟨f, S, hf, hS, _, _, heq⟩ := Network.integral_max_flow_min_cut N
    (fun _ => ⟨1, by simp [N, unitNetwork]⟩)
  obtain ⟨hg, hval⟩ := cancel_feasible_value s t hst f hf
  have hF : Separator G s t (boundary G S) := boundary_separates S hS.1 hS.2
  have hv : Spec.value N (fun a => (cancel f a : ℝ)) = ((boundary G S).card : ℝ) :=
    hval.trans (heq.trans (boundary_card_eq s t hst S).symm)
  by_cases hz : (boundary G S).card = 0
  · exact ⟨[], boundary G S, by simp [Packing], hF, by simpa using hz.symm⟩
  have hpos : 0 < Spec.value N (fun a => (cancel f a : ℝ)) := by
    rw [hv]
    exact_mod_cast (Nat.pos_of_ne_zero hz)
  obtain ⟨ps, cs, hd⟩ := (integer_flow_path_cycle_decomposition N
    (fun a => (cancel f a : ℝ)) hg
    (fun a => ⟨(cancel f a : ℤ), by simp⟩)).1 hpos
  change List (ℤ × Directed.Spec.path (dartGraph G) s t) at ps
  change List (ℤ × Directed.Spec.cycle (dartGraph G)) at cs
  change PathCycleSpec.IntegralDecomposes (G := dartGraph G) (s := s) (t := t)
    (fun a => (cancel f a : ℝ)) (Spec.value N (fun a => (cancel f a : ℝ))) ps cs at hd
  have hu : ∀ a : G.Dart, (cancel f a : ℤ) ≤ 1 := by
    intro a
    have hle : (cancel f a : ℝ) ≤ 1 := (hg.1 a).2
    exact_mod_cast hle
  have ho : ∀ a : G.Dart, (cancel f a : ℤ) = 0 ∨ (cancel f a.symm : ℤ) = 0 := by
    intro a
    rcases cancel_opposite f a with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  have hb (a : G.Dart) : pathLoad ps a ≤ (cancel f a : ℤ) := by
    have hload : (cancel f a : ℤ) =
        (ps.map fun p => PathCycleSpec.pathContribution p.1 p.2 a).sum +
          (cs.map fun c => Directed.CirculationSpec.contribution c.1 c.2 a).sum := by
      apply Int.cast_injective (α := ℝ)
      simpa only [Int.cast_natCast] using hd.2.2.2 a
    have hc : 0 ≤ (cs.map fun c => Directed.CirculationSpec.contribution c.1 c.2 a).sum := by
      apply List.sum_nonneg
      intro z hz
      obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hz
      have hcp := hd.2.1 c hcm
      unfold Directed.CirculationSpec.contribution
      split_ifs <;> omega
    change (ps.map fun p => PathCycleSpec.pathContribution p.1 p.2 a).sum ≤ _
    omega
  obtain ⟨hpack, hsum⟩ := packing_of_unit_load hst (fun a => (cancel f a : ℤ)) hu ho ps hd.1 hb
  have hlen : ps.length = (boundary G S).card := by
    have hw : (ps.length : ℝ) = ((boundary G S).card : ℝ) :=
      (congrArg (fun z : ℤ => (z : ℝ)) hsum).symm.trans (hd.2.2.1.trans hv)
    exact_mod_cast hw
  exact ⟨ps.map (fun p : ℤ × Directed.Spec.path (dartGraph G) s t => undirectPath p.2),
    boundary G S, hpack, hF,
    by simpa only [List.length_map] using hlen⟩

end Network


/-- W48, edge Menger: both extrema are attained and their natural values agree.
Only distinctness, with no nonadjacency hypothesis, is required. -/
theorem edge_menger : edge_menger_type.{u} := by
  intro V _ G s t hst
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨ps, F, hp, hF, heq⟩ := exists_equal_packing_separator (G := G) s t hst
  refine ⟨ps, F, hp, hF, heq, ?_, ?_⟩
  · intro qs hq
    rw [heq]
    exact packing_le_separator G s t qs F hq hF
  · intro D hD
    rw [← heq]
    exact packing_le_separator G s t ps D hp hD

end FiniteCombinatorics.Graph.EdgeMenger
