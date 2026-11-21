import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Euler.Closed
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Euler.Open
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Set.Card

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Euler
open SimpleGraph
open private countP_edges_eq_degree mem_support_of_reachable
  from MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Euler.Closed

/-- There is a longest trail with prescribed starting vertex. -/
private lemma exists_longest_trail_from {V : Type u} [Finite V]
    (G : SimpleGraph V) (a : V) :
    ∃ (b : V) (p : G.Walk a b), p.IsTrail ∧
      ∀ (c : V) (q : G.Walk a c), q.IsTrail → q.length ≤ p.length := by
  classical
  let _ := Fintype.ofFinite V
  let s := {n | ∃ (b : V) (p : G.Walk a b), p.IsTrail ∧ p.length = n}
  have hs : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    (fun n ⟨b, p, hp, hn⟩ => hn ▸ hp.length_le_card_edgeFinset)
  obtain ⟨n, ⟨⟨b, p, hp, rfl⟩, hn⟩⟩ :=
    hs.exists_maximal ⟨0, ⟨a, Walk.nil, by simp⟩⟩
  refine ⟨b, p, hp, fun c q hq => ?_⟩
  have h := hn ⟨c, q, hq, rfl⟩
  omega

private lemma longest_from_saturated {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsTrail)
    (hm : ∀ (c : V) (q : G.Walk a c), q.IsTrail → q.length ≤ p.length) :
    ∀ w, G.Adj b w → s(b, w) ∈ p.edges := by
  classical
  intro w hw
  by_contra he
  have h := hm w (p.concat hw) (hp.concat hw he)
  simp only [Walk.length_concat] at h
  omega

private lemma longest_from_closed {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (heven : ∀ v, Even (G.degree v))
    {a b : V} (p : G.Walk a b) (hp : p.IsTrail)
    (hm : ∀ (c : V) (q : G.Walk a c), q.IsTrail → q.length ≤ p.length) : a = b := by
  have hc := countP_edges_eq_degree G p hp (longest_from_saturated p hp hm)
  have hh := (hp.even_countP_edges_iff b).mp (hc.symm ▸ heven b)
  by_contra hab
  exact (hh hab).2 rfl

/-- Deleting a trail partitions every incidence set into used and unused edges. -/
private lemma degree_unused_add_used {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (p : G.Walk a b)
    (hp : p.IsTrail) (x : V) [DecidableRel (G.deleteEdges p.edgeSet).Adj] :
    (G.deleteEdges p.edgeSet).degree x + (p.edges.countP fun e => x ∈ e) =
      G.degree x := by
  classical
  have hu : (G.deleteEdges p.edgeSet).incidenceFinset x =
      (G.incidenceFinset x).filter (fun e => e ∉ p.edges) := by
    ext e
    simp only [Finset.mem_filter, mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq,
      edgeSet_deleteEdges, Set.mem_sdiff, Walk.mem_edgeSet]
    tauto
  have ht : hp.edgesFinset.filter (fun e => x ∈ e) =
      (G.incidenceFinset x).filter (fun e => e ∈ p.edges) := by
    ext e
    simp only [Finset.mem_filter, Walk.IsTrail.edgesFinset, Finset.mem_mk,
      Multiset.mem_coe, mem_incidenceFinset]
    constructor
    · rintro ⟨he, hx⟩
      exact ⟨⟨p.edges_subset_edgeSet he, hx⟩, he⟩
    · rintro ⟨⟨_, hx⟩, he⟩
      exact ⟨he, hx⟩
  have hc : (p.edges.countP fun e => x ∈ e) =
      (hp.edgesFinset.filter (fun e => x ∈ e)).card := by
    simp [Finset.card_def, Multiset.countP_eq_card_filter, ← Multiset.coe_countP]
  rw [← card_incidenceFinset_eq_degree, hu, hc, ht,
    ← card_incidenceFinset_eq_degree]
  simpa only [Nat.add_comm] using
    (Finset.card_filter_add_card_filter_not (s := G.incidenceFinset x) (fun e => e ∈ p.edges))

/-- In an even graph, a longest trail from a specified vertex is closed. -/
private lemma exists_closed_trail_from {V : Type u} [Finite V]
    (G : SimpleGraph V) (heven : ∀ v, Even (FiniteCombinatorics.Graph.degree G v)) (x : V) :
    ∃ (q : G.Walk x x), q.IsTrail ∧
      ∀ (c : V) (r : G.Walk x c), r.IsTrail → r.length ≤ q.length := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨y, q, hq, hm⟩ := exists_longest_trail_from G x
  have hxy := longest_from_closed G
    (fun v => (degree_mathlib G v) ▸ heven v) q hq hm
  subst y
  exact ⟨q, hq, hm⟩

/-- A closed trail of unused edges can be inserted at any visited vertex.
Thus a longest trail whose unused degrees are all even is saturated everywhere. -/
private lemma longest_from_saturated_support {V : Type u} [Finite V]
    (G : SimpleGraph V) {a b : V} (p : G.Walk a b) (hp : p.IsTrail)
    (hm : ∀ (c : V) (q : G.Walk a c), q.IsTrail → q.length ≤ p.length)
    (heven : ∀ v, Even (FiniteCombinatorics.Graph.degree (G.deleteEdges p.edgeSet) v)) :
    ∀ x ∈ p.support, ∀ y, G.Adj x y → s(x, y) ∈ p.edges := by
  classical
  intro x hx y hxy
  by_contra hused
  let R := G.deleteEdges p.edgeSet
  have hR : R.Adj x y := (G.deleteEdges_adj).mpr ⟨hxy, hused⟩
  obtain ⟨q, hq, hqm⟩ := exists_closed_trail_from R heven x
  have hpos : 1 ≤ q.length := by
    have h := hqm y (.cons hR .nil) (by simp)
    simpa only [Walk.length_cons, Walk.length_nil, zero_add] using h
  let r := q.mapLe (G.deleteEdges_le p.edgeSet)
  have hr : r.IsTrail := hq.mapLe _
  have hd : p.edges.Disjoint r.edges := by
    apply List.disjoint_left.mpr
    intro e hep her
    have heR := q.edges_subset_edgeSet (by simpa only [r, Walk.edges_mapLe_eq_edges] using her)
    have hnot : e ∉ p.edgeSet := (edgeSet_deleteEdges p.edgeSet ▸ heR).2
    exact hnot hep
  have hpref : ((p.takeUntil x hx).append r).IsTrail := by
    rw [Walk.isTrail_append]
    exact ⟨hp.takeUntil hx, hr, List.disjoint_left.mpr
      (fun e he her => (List.disjoint_left.mp hd) (p.edges_takeUntil_subset_edges hx he) her)⟩
  have hins : (((p.takeUntil x hx).append r).append (p.dropUntil x hx)).IsTrail := by
    rw [Walk.isTrail_append]
    refine ⟨hpref, hp.dropUntil hx, List.disjoint_left.mpr ?_⟩
    intro e he hes
    rw [Walk.edges_append] at he
    rcases List.mem_append.mp he with he | he
    · exact (List.disjoint_left.mp (hp.disjoint_edges_takeUntil_dropUntil hx)) he hes
    · exact (List.disjoint_left.mp hd) (p.edges_dropUntil_subset_edges hx hes) he
  have hlong := hm b _ hins
  have hsplit := congrArg Walk.length (p.take_spec hx)
  simp only [Walk.length_append, r, Walk.length_mapLe] at hlong hsplit
  omega

theorem open_eulerTrail_odd_degree :
    Specs.FiniteCombinatorics.Graph.Euler.Open.open_eulerTrail_odd_degreeType := by
  intro V _ G a b p hp hab w
  classical
  let _ := Fintype.ofFinite V
  rw [degree_mathlib G w, ← Nat.not_even_iff_odd,
    ((eulerTrail_mathlib G p).mp hp).even_degree_iff]
  change ¬ (a ≠ b → w ≠ a ∧ w ≠ b) ↔ _
  tauto

/-- W39: the two odd vertices can be prescribed in either order. -/
theorem exists_eulerTrail_of_odd_endpoints :
    Specs.FiniteCombinatorics.Graph.Euler.Open.exists_eulerTrail_of_odd_endpointsType := by
  intro V _ G _he hconn a b hab hodd
  classical
  let _ := Fintype.ofFinite V
  have ha : Odd (G.degree a) := by
    rw [← degree_mathlib G a]
    exact (hodd a).mpr (Or.inl rfl)
  obtain ⟨c, p, hp, hm⟩ := exists_longest_trail_from G a
  have hc := countP_edges_eq_degree G p hp (longest_from_saturated p hp hm)
  have hac : a ≠ c := by
    intro h
    subst c
    have hcount : Even (p.edges.countP fun e => a ∈ e) :=
      (hp.even_countP_edges_iff a).mpr (by simp)
    exact (Nat.not_even_iff_odd.mpr ha) (hc ▸ hcount)
  have hcodd : Odd (G.degree c) := by
    rw [← Nat.not_even_iff_odd, ← hc, hp.even_countP_edges_iff]
    exact fun h => (h hac).2 rfl
  have hcb : c = b := by
    have h := (hodd c).mp (by simpa only [degree_mathlib G c] using hcodd)
    exact h.resolve_left (Ne.symm hac)
  subst c
  have heven : ∀ x, Even (FiniteCombinatorics.Graph.degree (G.deleteEdges p.edgeSet) x) := by
    intro x
    change Even (Specs.FiniteCombinatorics.Graph.Foundations.degreeValue (G.deleteEdges p.edgeSet) x)
    rw [degree_mathlib]
    have hsum := degree_unused_add_used G p hp x
    have hle : (p.edges.countP fun e => x ∈ e) ≤ G.degree x := by omega
    have heq : (G.deleteEdges p.edgeSet).degree x =
        G.degree x - (p.edges.countP fun e => x ∈ e) := by omega
    rw [heq, Nat.even_sub' hle]
    simp only [← Nat.not_even_iff_odd, hp.even_countP_edges_iff,
      ← degree_mathlib G x]
    have ho := hodd x
    rw [← Nat.not_even_iff_odd] at ho
    tauto
  have hs := longest_from_saturated_support G p hp hm heven
  have hapos : a ∈ edgeSupportVertices G := by
    change 0 < Specs.FiniteCombinatorics.Graph.Foundations.degreeValue G a
    rw [degree_mathlib]
    exact Nat.pos_of_ne_zero (fun hz => by simpa [hz] using ha)
  refine ⟨p, ⟨hp, ?_⟩, hab⟩
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have hx : x ∈ edgeSupportVertices G :=
      (edgeSupportVertices_iff_exists_adj G x).mpr ⟨y, he⟩
    have hax : G.Reachable a x := (hconn ⟨a, hapos⟩ ⟨x, hx⟩).map
      (Embedding.induce (edgeSupportVertices G)).toHom
    exact hs x (mem_support_of_reachable p hs p.start_mem_support hax) y he

theorem open_eulerTrail_iff_two_odd_degree :
    Specs.FiniteCombinatorics.Graph.Euler.Open.open_eulerTrail_iff_two_odd_degreeType := by
  intro V _ G he hconn
  constructor
  · rintro ⟨a, b, p, hp, hab⟩
    exact ⟨a, b, hab, open_eulerTrail_odd_degree G p hp hab⟩
  · rintro ⟨a, b, hab, hodd⟩
    obtain ⟨p, hp⟩ := exists_eulerTrail_of_odd_endpoints G he hconn a b hab hodd
    exact ⟨a, b, p, hp⟩

/-- The cardinal form of W39: exactly two vertices have odd degree. -/
theorem open_eulerTrail_iff_card_odd_degree :
    Specs.FiniteCombinatorics.Graph.Euler.Open.open_eulerTrail_iff_card_odd_degreeType := by
  intro V _ G he hconn
  classical
  rw [open_eulerTrail_iff_two_odd_degree G he hconn]
  let O : Set V := {w | Odd (Specs.FiniteCombinatorics.Graph.Foundations.degreeValue G w)}
  change _ ↔ Nat.card O = 2
  rw [Nat.card_coe_set_eq, Set.ncard_eq_two]
  constructor
  · rintro ⟨a, b, hab, hodd⟩
    refine ⟨a, b, hab, ?_⟩
    ext w
    exact (hodd w).trans (by simp)
  · rintro ⟨a, b, hab, hO⟩
    refine ⟨a, b, hab, ?_⟩
    intro w
    change w ∈ O ↔ _
    rw [hO]
    simp

end FiniteCombinatorics.Graph.Euler
