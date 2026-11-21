import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Connectivity.Whitney
import Mathlib.Tactic.Push

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Connectivity

abbrev VertexCut : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.VertexCutType :=
  Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.VertexCutValue
abbrev EdgeCut : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.EdgeCutType :=
  Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.EdgeCutValue
abbrev vertexConnectivity : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.connectivityType :=
  Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.vertexConnectivityValue
abbrev edgeConnectivity : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.connectivityType :=
  Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.edgeConnectivityValue
abbrev minimumDegree : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.connectivityType :=
  Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.minimumDegreeValue

variable {V : Type u} [Finite V] (G : SimpleGraph V)

lemma vertexConnectivity_le {s : Set V} (hs : VertexCut G s) :
    vertexConnectivity G ≤ s.ncard := Nat.sInf_le ⟨s, hs, rfl⟩

lemma edgeConnectivity_le {s : Set (Sym2 V)} (hs : EdgeCut G s) :
    edgeConnectivity G ≤ s.ncard := Nat.sInf_le ⟨s, hs, rfl⟩

omit [Finite V] in
lemma nonempty_of_order (hn : 2 ≤ Nat.card V) : Nonempty V := by
  exact (Nat.card_pos_iff.mp (by omega)).1

lemma vertex_cut_compl_singleton (v : V) : VertexCut G ({v}ᶜ) := by
  right
  simp

lemma vertexConnectivity_le_order_sub_one (v : V) :
    vertexConnectivity G ≤ Nat.card V - 1 := by
  have h := vertexConnectivity_le G (vertex_cut_compl_singleton G v)
  simpa [Set.ncard_compl] using h

theorem vertex_minimum : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.vertex_minimumType := by
  intro V _ G hn
  obtain ⟨v⟩ := nonempty_of_order hn
  obtain ⟨s, hs, he⟩ := Nat.sInf_mem
    (s := {k | ∃ s, VertexCut G s ∧ s.ncard = k})
    ⟨_, {v}ᶜ, vertex_cut_compl_singleton G v, rfl⟩
  exact ⟨s, hs, he, fun t ht => vertexConnectivity_le G ht⟩

lemma incidence_is_cut (v w : V) (hvw : v ≠ w) : EdgeCut G (G.incidenceSet v) := by
  refine ⟨G.incidenceSet_subset _, fun hc => ?_⟩
  have h : (G.deleteEdges (G.incidenceSet v)).neighborSet v = ∅ := by
    ext x
    simp [SimpleGraph.mem_neighborSet]
  exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hvw h (hc v w)

theorem edge_minimum : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.edge_minimumType := by
  intro V _ G hn
  have : Nonempty V := nonempty_of_order hn
  have : Nontrivial V := by
    let := Fintype.ofFinite V
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨s, hs, he⟩ := Nat.sInf_mem
    (s := {k | ∃ s, EdgeCut G s ∧ s.ncard = k})
    ⟨_, G.incidenceSet v, incidence_is_cut G v w hw.symm, rfl⟩
  exact ⟨s, hs, he, fun t ht => edgeConnectivity_le G ht⟩

theorem degree_minimum : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.degree_minimumType := by
  intro V _ G hn
  have : Nonempty V := nonempty_of_order hn
  obtain ⟨v, hv⟩ := Nat.sInf_mem (Set.range_nonempty (fun v => Nat.card (G.neighborSet v)))
  exact ⟨v, hv, fun w => Nat.sInf_le (Set.mem_range_self w)⟩

theorem disconnected_values : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.disconnected_valuesType := by
  intro V _ G hG
  have hv : VertexCut G ∅ := by
    left
    intro hc
    apply hG
    exact hc.map ⟨Subtype.val, fun h => h⟩ (by intro v; exact ⟨⟨v, by simp⟩, rfl⟩)
  have he : EdgeCut G ∅ := by simpa [EdgeCut, Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.EdgeCutValue] using And.intro (Set.empty_subset G.edgeSet) hG
  exact ⟨Nat.eq_zero_of_le_zero (by simpa using vertexConnectivity_le G hv),
    Nat.eq_zero_of_le_zero (by simpa using edgeConnectivity_le G he)⟩

/- The ordered representation counts every crossing edge once, since the
two endpoints belong to disjoint sides of the partition. -/
private abbrev CrossingEdges (S : Set V) :=
  {p : S × ↥(Sᶜ) // G.Adj p.1 p.2}

omit [Finite V] in
private lemma crossing_pair_injective (S : Set V) :
    Function.Injective (fun p : S × ↥(Sᶜ) => s(p.1.val, p.2.val)) := by
  intro p q hpq
  rcases Sym2.eq_iff.mp hpq with h | h
  · exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  · exact False.elim (q.2.property (h.1 ▸ p.1.property))

private lemma crossing_card_le (S : Set V) (E : Set (Sym2 V))
    (hE : ∀ (x : S) (y : ↥(Sᶜ)), G.Adj x y → s(x.val, y.val) ∈ E) :
    Nat.card (CrossingEdges G S) ≤ E.ncard := by
  let f : CrossingEdges G S → E := fun e => ⟨s(e.val.1.val, e.val.2.val), hE _ _ e.property⟩
  exact Nat.card_le_card_of_injective f (fun a b h =>
    Subtype.ext (crossing_pair_injective S (congrArg Subtype.val h)))

private lemma reachable_mem_of_closed {W : Type*} {H : SimpleGraph W} (S : Set W)
    (hS : ∀ x ∈ S, ∀ y, H.Adj x y → y ∈ S) {x y : W}
    (hr : H.Reachable x y) (hx : x ∈ S) : y ∈ S := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hx
  | cons h p ih => exact ih (hS _ hx _ h)

private lemma vertexConnectivity_le_crossing (S : Set V)
    (hS : S.Nonempty) (hT : Sᶜ.Nonempty) :
    vertexConnectivity G ≤ Nat.card (CrossingEdges G S) := by
  classical
  by_cases hall : ∀ (x : S) (y : ↥(Sᶜ)), G.Adj x y
  · let e : CrossingEdges G S ≃ S × ↥(Sᶜ) :=
      { toFun := Subtype.val
        invFun := fun p => ⟨p, hall p.1 p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hcard : Nat.card (CrossingEdges G S) = S.ncard * Sᶜ.ncard :=
      (Nat.card_congr e).trans (Nat.card_prod _ _)
    have ha := hS.ncard_pos
    have hb := hT.ncard_pos
    obtain ⟨v, hv⟩ := hS
    have hκ := vertexConnectivity_le_order_sub_one G v
    have hsum := Set.ncard_add_ncard_compl S
    rw [hcard]
    have : Nat.card V - 1 ≤ S.ncard * Sᶜ.ncard := by
      obtain ⟨a, haeq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
      obtain ⟨b, hbeq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
      have hn : Nat.card V = a + b + 2 := by omega
      rw [haeq, hbeq, hn]
      simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    exact hκ.trans this
  · push Not at hall
    obtain ⟨u, v, huv⟩ := hall
    -- Choose one endpoint of each crossing edge, avoiding u and v.
    let f : CrossingEdges G S → V := fun e =>
      if e.val.1.val = u.val then e.val.2.val else e.val.1.val
    let C : Set V := Set.range f
    have hu : u.val ∉ C := by
      rintro ⟨e, he⟩
      dsimp [f] at he
      split_ifs at he with h
      · exact e.val.2.property (he ▸ u.property)
      · exact h he
    have hv : v.val ∉ C := by
      rintro ⟨e, he⟩
      dsimp [f] at he
      split_ifs at he with h
      · exact huv (by simpa [h, he] using e.property)
      · exact v.property (he ▸ e.val.1.property)
    have hclosed : ∀ (x : ↥(Cᶜ)), x.val ∈ S → ∀ (y : ↥(Cᶜ)),
        (G.induce Cᶜ).Adj x y → y.val ∈ S := by
      intro x hx y hxy
      by_contra hy
      let e : CrossingEdges G S := ⟨(⟨x.val, hx⟩, ⟨y.val, hy⟩), hxy⟩
      have he : f e ∈ C := Set.mem_range_self e
      dsimp [f, e] at he
      split_ifs at he
      · exact y.property he
      · exact x.property he
    have hcut : VertexCut G C := by
      left
      intro hc
      have h := reachable_mem_of_closed {x : ↥(Cᶜ) | x.val ∈ S}
        (fun x hx y hxy => hclosed x hx y hxy)
        (hc ⟨u.val, hu⟩ ⟨v.val, hv⟩) u.property
      exact v.property h
    apply (vertexConnectivity_le G hcut).trans
    exact Nat.card_le_card_of_surjective (fun e => (⟨f e, Set.mem_range_self e⟩ : C))
      (by rintro ⟨x, e, rfl⟩; exact ⟨e, rfl⟩)

theorem whitney_bounds : Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.whitney_boundsType := by
  intro V _ G hn
  classical
  have : Nonempty V := nonempty_of_order hn
  have : Nontrivial V := by
    let := Fintype.ofFinite V
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [← Nat.card_eq_fintype_card]
    omega
  constructor
  · obtain ⟨E, hE, hcard, _⟩ := edge_minimum G hn
    have hnp : ¬(G.deleteEdges E).Preconnected := fun hp => hE.2 ⟨hp⟩
    change ¬∀ u v, (G.deleteEdges E).Reachable u v at hnp
    push Not at hnp
    obtain ⟨u, v, huv⟩ := hnp
    let S : Set V := {x | (G.deleteEdges E).Reachable u x}
    calc vertexConnectivity G
      _ ≤ Nat.card (CrossingEdges G S) :=
        vertexConnectivity_le_crossing G S ⟨u, .rfl⟩ ⟨v, huv⟩
      _ ≤ E.ncard := crossing_card_le G S E (by
        intro x y hxy
        by_contra he
        exact y.property (x.property.trans (SimpleGraph.deleteEdges_adj.mpr ⟨hxy, he⟩).reachable))
      _ = edgeConnectivity G := hcard
  · obtain ⟨v, hv, _⟩ := degree_minimum G hn
    obtain ⟨w, hw⟩ := exists_ne v
    calc edgeConnectivity G
      _ ≤ (G.incidenceSet v).ncard := edgeConnectivity_le G (incidence_is_cut G v w hw.symm)
      _ = Nat.card (G.neighborSet v) := Nat.card_congr (G.incidenceSetEquivNeighborSet v)
      _ = minimumDegree G := hv

theorem complete_vertexConnectivity :
    Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.complete_vertexConnectivityType := by
  intro V _ hn
  classical
  obtain ⟨v⟩ := nonempty_of_order hn
  apply le_antisymm (vertexConnectivity_le_order_sub_one (⊤ : SimpleGraph V) v)
  obtain ⟨s, hs, he, _⟩ := vertex_minimum (⊤ : SimpleGraph V) hn
  change Nat.card V - 1 ≤ Specs.FiniteCombinatorics.Graph.Connectivity.Whitney.vertexConnectivityValue (⊤ : SimpleGraph V)
  rw [← he]
  have hsum := Set.ncard_add_ncard_compl s
  rcases hs with hs | hs
  · have hempty : sᶜ = ∅ := by
      by_contra hne
      have : Nonempty ↥(sᶜ) := (Set.nonempty_iff_ne_empty.mpr hne).coe_sort
      exact hs (by simp)
    have hz : sᶜ.ncard = 0 := by rw [hempty]; simp
    omega
  · omega

end FiniteCombinatorics.Graph.Connectivity
