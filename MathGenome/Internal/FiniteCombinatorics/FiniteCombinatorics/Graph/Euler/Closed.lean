import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Euler.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Euler.Closed
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Euler
open SimpleGraph

/-- At a saturated endpoint, the number of used incident edges is its degree. -/
private lemma countP_edges_eq_degree {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (p : G.Walk a b)
    (hp : p.IsTrail) (hs : ∀ w, G.Adj b w → s(b, w) ∈ p.edges) :
    (p.edges.countP fun e => b ∈ e) = G.degree b := by
  have hfin : hp.edgesFinset.filter (fun e => b ∈ e) = G.incidenceFinset b := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_filter, Walk.IsTrail.edgesFinset, Finset.mem_mk,
        Multiset.mem_coe, mem_incidenceFinset, mk'_mem_incidenceSet_iff, Sym2.mem_iff]
      constructor
      · rintro ⟨he, hb⟩
        exact ⟨p.edges_subset_edgeSet he, hb⟩
      · rintro ⟨hxy, rfl | rfl⟩
        · exact ⟨hs y hxy, Or.inl rfl⟩
        · exact ⟨by simpa only [Sym2.eq_swap] using hs x hxy.symm, Or.inr rfl⟩
  rw [← card_incidenceFinset_eq_degree, ← hfin]
  simp [Finset.card_def, Multiset.countP_eq_card_filter, ← Multiset.coe_countP]

/-- A longest trail cannot be extended by an unused edge at its endpoint. -/
private lemma longest_trail_saturated {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsTrail)
    (hm : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length) :
    ∀ w, G.Adj b w → s(b, w) ∈ p.edges := by
  classical
  intro w hw
  by_contra he
  have h := hm a w (p.concat hw) (hp.concat hw he)
  simp only [Walk.length_concat] at h
  omega

/-- Even degrees force a longest trail to close. -/
private lemma longest_trail_closed {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v))
    {a b : V} (p : G.Walk a b) (hp : p.IsTrail)
    (hm : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length) : a = b := by
  have hc := countP_edges_eq_degree G p hp (longest_trail_saturated p hp hm)
  have hh := (hp.even_countP_edges_iff b).mp (hc.symm ▸ heven b)
  by_contra hab
  exact (hh hab).2 rfl

/-- Rotation makes every visited vertex of a longest closed trail saturated. -/
private lemma longest_closed_saturated {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {a : V} (p : G.Walk a a) (hp : p.IsTrail)
    (hm : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length)
    {v : V} (hv : v ∈ p.support) :
    ∀ w, G.Adj v w → s(v, w) ∈ p.edges := by
  intro w hw
  have hr := longest_trail_saturated (p.rotate v hv) (hp.rotate hv)
    (fun x y q hq => by simpa using hm x y q hq) w hw
  exact (p.rotate_edges v hv).mem_iff.mp hr

/-- Saturation propagates membership in a trail's support along any walk. -/
private lemma mem_support_of_reachable {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b)
    (hs : ∀ v ∈ p.support, ∀ w, G.Adj v w → s(v, w) ∈ p.edges)
    {x y : V} (hx : x ∈ p.support) (hxy : G.Reachable x y) : y ∈ p.support := by
  obtain ⟨q⟩ := hxy
  induction q with
  | nil => exact hx
  | @cons x z y h q ih =>
    exact ih (p.snd_mem_support_of_mem_edges (hs x hx z h))

theorem closed_eulerTrail_even_degree :
    Specs.FiniteCombinatorics.Graph.Euler.Closed.closed_eulerTrail_even_degreeType := by
  intro V _ G a p hp v
  classical
  let _ := Fintype.ofFinite V
  rw [degree_mathlib G v]
  exact (((eulerTrail_mathlib G p).mp hp).even_degree_iff).mpr (by simp)

theorem eulerTrail_edgeSupport_connected :
    Specs.FiniteCombinatorics.Graph.Euler.Closed.eulerTrail_edgeSupport_connectedType := by
  intro V _ G he a b p hp
  classical
  have hE := (eulerTrail_mathlib G p).mp hp
  have hn : ¬p.Nil := by
    intro hn
    have hz := hE.nil_iff.mp hn
    simp [hz] at he
  have hs : {v | v ∈ p.support} = edgeSupportVertices G := by
    ext v
    exact (hE.mem_support_iff hn).trans
      (exists_adj_iff_not_isIsolated.symm.trans
        (edgeSupportVertices_iff_exists_adj G v).symm)
  change (G.induce (edgeSupportVertices G)).Connected
  rw [← hs]
  exact p.connected_induce_support

/-- W39: a finite graph with connected, nonempty edge support has a closed
Euler trail precisely when every degree is even. -/
theorem closed_eulerTrail_iff_even_degree :
    Specs.FiniteCombinatorics.Graph.Euler.Closed.closed_eulerTrail_iff_even_degreeType := by
  intro V _ G he hconn
  classical
  constructor
  · rintro ⟨a, p, hp, _⟩
    exact closed_eulerTrail_even_degree G a p hp
  · intro heven
    let _ := Fintype.ofFinite V
    have : Nonempty V := by
      obtain ⟨e, he⟩ := he
      induction e using Sym2.ind with
      | _ x y => exact ⟨x⟩
    obtain ⟨a, b, p, hp, hm⟩ := Walk.exists_isTrail_forall_isTrail_length_le_length G
    have hab := longest_trail_closed G (fun v => by simpa only [← degree_mathlib G v] using heven v)
      p hp hm
    subst b
    have hs : ∀ v ∈ p.support, ∀ w, G.Adj v w → s(v, w) ∈ p.edges :=
      fun v hv => longest_closed_saturated p hp hm hv
    have hn : ¬p.Nil := by
      intro hn
      obtain ⟨e, he⟩ := he
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : G.Adj x y := he
        have ht : (Walk.cons hxy Walk.nil).IsTrail := ⟨by simp⟩
        have h : 1 ≤ p.length := hm x y (Walk.cons hxy Walk.nil) ht
        have hz := hn.length_eq_zero
        omega
    have ha : a ∈ edgeSupportVertices G :=
      (edgeSupportVertices_iff_exists_adj G a).mpr ⟨p.snd, p.adj_snd hn⟩
    refine ⟨a, p, ⟨hp, ?_⟩, rfl⟩
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ edgeSupportVertices G :=
        (edgeSupportVertices_iff_exists_adj G x).mpr ⟨y, he⟩
      have hax : G.Reachable a x := (hconn ⟨a, ha⟩ ⟨x, hx⟩).map
        (Embedding.induce (edgeSupportVertices G)).toHom
      exact hs x (mem_support_of_reachable p hs p.start_mem_support hax) y he

end FiniteCombinatorics.Graph.Euler
