import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Berge

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Matching

abbrev flipAlong : Specs.FiniteCombinatorics.Graph.Matching.Berge.flipAlongType :=
  Specs.FiniteCombinatorics.Graph.Matching.Berge.flipAlongValue

variable {V : Type u} [Finite V] {G : SimpleGraph V} {M : Set (Sym2 V)}
  {a b : V} {p : G.Walk a b}

theorem augmenting_length_odd (h : IsAugmentingPath G M p) : p.length % 2 = 1 := by
  have hp := h.2.2.1
  have hi := h.2.2.2.2.2.1 (p.length - 1) (by omega)
  have hn := h.2.2.2.2.2.2
  rw [show p.length - 1 + 1 = p.length by omega, p.getVert_length] at hi
  have : (p.length - 1) % 2 ≠ 1 := fun hh => hn (hi.mpr hh)
  omega

omit [Finite V] in
/-- An edge occurrence with its zero-based index. -/
private theorem edge_index {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ i < p.length, e = s(p.getVert i, p.getVert (i + 1)) := by
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
  exact ⟨i, by simpa using hi, hie.symm.trans (SimpleGraph.Walk.getElem_edges hi)⟩

/-- Edges outside M on an augmenting path have even indices. -/
private theorem outside_index (h : IsAugmentingPath G M p) {i : ℕ} (hi : i < p.length)
    (hn : s(p.getVert i, p.getVert (i + 1)) ∉ M) : i % 2 = 0 := by
  have hx := h.2.2.2.2.2.1 i hi
  have : i % 2 ≠ 1 := fun hm => hn (hx.mpr hm)
  omega

/-- The new path edges are pairwise vertex-disjoint. -/
theorem augmenting_new_edges_disjoint (h : IsAugmentingPath G M p)
    {e f : Sym2 V} (he : e ∈ p.edges ∧ e ∉ M) (hf : f ∈ p.edges ∧ f ∉ M)
    {v : V} (hve : v ∈ e) (hvf : v ∈ f) : e = f := by
  obtain ⟨i, hi, rfl⟩ := edge_index he.1
  obtain ⟨j, hj, rfl⟩ := edge_index hf.1
  have hieven := outside_index h hi he.2
  have hjeven := outside_index h hj hf.2
  have hp := h.2.1.getVert_injOn
  rcases Sym2.mem_iff.mp hve with hv | hv <;>
    rcases Sym2.mem_iff.mp hvf with hw | hw
  · have hij : i = j := hp (by exact Nat.le_of_lt hi) (by exact Nat.le_of_lt hj)
      (hv.symm.trans hw)
    rw [hij]
  · have hij : i = j + 1 := hp (by exact Nat.le_of_lt hi) (by exact hj)
      (hv.symm.trans hw)
    omega
  · have hij : i + 1 = j := hp (by exact hi) (by exact Nat.le_of_lt hj)
      (hv.symm.trans hw)
    omega
  · have hij : i + 1 = j + 1 := hp (by exact hi) (by exact hj)
      (hv.symm.trans hw)
    have : i = j := by omega
    rw [this]

/-- Every old matching edge at a vertex of a new path edge is removed. -/
theorem augmenting_incident_matching_edge_on_path (h : IsAugmentingPath G M p)
    {e f : Sym2 V} (he : e ∈ p.edges ∧ e ∉ M) (hf : f ∈ M)
    {v : V} (hve : v ∈ e) (hvf : v ∈ f) : f ∈ p.edges := by
  obtain ⟨i, hi, rfl⟩ := edge_index he.1
  have hieven := outside_index h hi he.2
  rcases Sym2.mem_iff.mp hve with rfl | rfl
  · by_cases hz : i = 0
    · have hs : Saturated M a := by
        refine ⟨f, hf, ?_⟩
        simpa [hz] using hvf
      exact (h.2.2.2.1 hs).elim
    · have hj : i - 1 < p.length := by omega
      have hm := (h.2.2.2.2.2.1 (i - 1) hj).mpr (by omega)
      have heq : i - 1 + 1 = i := by omega
      rw [heq] at hm
      have hfe := h.1.2 f hf _ hm (p.getVert i) hvf (Sym2.mem_mk_right _ _)
      rw [hfe]
      apply p.mk_mem_edges_iff_exists.mpr
      exact ⟨i - 1, hj, by rw [heq]⟩
  · by_cases hend : i + 1 = p.length
    · have hs : Saturated M b := by
        refine ⟨f, hf, ?_⟩
        simpa [hend] using hvf
      exact (h.2.2.2.2.1 hs).elim
    · have hj : i + 1 < p.length := by omega
      have hm := (h.2.2.2.2.2.1 (i + 1) hj).mpr (by omega)
      have hfe := h.1.2 f hf _ hm (p.getVert (i + 1)) hvf
        (Sym2.mem_mk_left _ _)
      rw [hfe]
      exact p.mk_mem_edges_iff_exists.mpr ⟨i + 1, hj, rfl⟩

/-- Toggling an augmenting path preserves the matching property. -/
theorem flipAlong_isMatching (h : IsAugmentingPath G M p) :
    IsMatching G (flipAlong M p) := by
  constructor
  · intro e he
    rcases he with he | he
    · exact h.1.1 he.1
    · exact p.edges_subset_edgeSet he.1
  · intro e he f hf v hve hvf
    rcases he with he | he <;> rcases hf with hf | hf
    · exact h.1.2 e he.1 f hf.1 v hve hvf
    · exact (he.2 (augmenting_incident_matching_edge_on_path h hf he.1 hvf hve)).elim
    · exact (hf.2 (augmenting_incident_matching_edge_on_path h he hf.1 hve hvf)).elim
    · exact augmenting_new_edges_disjoint h he hf hve hvf

/-- An odd list alternating outside/inside has one extra outside entry. -/
private theorem alternating_count {α : Type*} (l : List α) (P : α → Prop)
    [DecidablePred P]
    (halt : ∀ i (hi : i < l.length), P l[i] ↔ i % 2 = 1)
    (hodd : l.length % 2 = 1) :
    l.countP (fun e => decide (¬ P e)) = l.countP (fun e => decide (P e)) + 1 := by
  induction l using List.twoStepInduction with
  | nil => simp at hodd
  | singleton x =>
    have hx : ¬ P x := by
      have hh := halt 0 (by simp)
      simpa only [List.getElem_cons_zero, Nat.zero_mod, Nat.zero_ne_one, iff_false] using hh
    simp [hx]
  | cons_cons x y l ih _ =>
    have hx : ¬ P x := by
      have hh := halt 0 (by simp)
      simpa only [List.getElem_cons_zero, Nat.zero_mod, Nat.zero_ne_one, iff_false] using hh
    have hy : P y := (halt 1 (by simp)).mpr (by decide)
    have hl : ∀ i (hi : i < l.length), P l[i] ↔ i % 2 = 1 := by
      intro i hi
      have he := halt (i + 2) (by simp; omega)
      simpa [Nat.add_mod] using he
    have ho : l.length % 2 = 1 := by
      simp only [List.length_cons] at hodd
      omega
    simpa [hx, hy] using ih hl ho

/-- The path adds exactly one more edge than it removes. -/
theorem augmenting_path_edge_balance (h : IsAugmentingPath G M p) :
    (p.edgeSet \ M).ncard = (p.edgeSet ∩ M).ncard + 1 := by
  classical
  have hc := alternating_count p.edges (fun e => e ∈ M) (by
    intro i hi
    rw [SimpleGraph.Walk.getElem_edges hi]
    exact h.2.2.2.2.2.1 i (by simpa using hi))
    (by simpa using augmenting_length_odd h)
  have hnew : p.edgeSet \ M =
      (p.edges.toFinset.filter (fun e => e ∉ M) : Set (Sym2 V)) := by
    ext e
    simp
  have hold : p.edgeSet ∩ M =
      (p.edges.toFinset.filter (fun e => e ∈ M) : Set (Sym2 V)) := by
    ext e
    simp
  rw [hnew, hold, Set.ncard_coe_finset, Set.ncard_coe_finset,
    h.2.1.edges_nodup.card_eq_countP, h.2.1.edges_nodup.card_eq_countP]
  exact hc

/-- The explicit flip has exactly one additional edge. -/
theorem flipAlong_card (h : IsAugmentingPath G M p) :
    Nat.card (flipAlong M p) = Nat.card M + 1 := by
  have hbal := augmenting_path_edge_balance h
  have hpart := Set.ncard_inter_add_ncard_sdiff_eq_ncard M p.edgeSet
  have hdisj : Disjoint (M \ p.edgeSet) (p.edgeSet \ M) := by
    exact Set.disjoint_left.mpr (fun _ he hf => he.2 hf.1)
  change ((M \ p.edgeSet) ∪ (p.edgeSet \ M)).ncard = M.ncard + 1
  rw [Set.ncard_union_eq hdisj]
  rw [Set.inter_comm] at hpart
  omega

theorem flip_augmenting :
    Specs.FiniteCombinatorics.Graph.Matching.Berge.flip_augmentingType := by
  intro V _ G M a b p h
  exact ⟨flipAlong_isMatching h, flipAlong_card h⟩

/-- Consequently, maximum matchings admit no augmenting path. -/
theorem maximum_has_no_augmenting_path (_hM : IsMatching G M)
    (hmax : ∀ N : Set (Sym2 V), IsMatching G N → Nat.card N ≤ Nat.card M) :
    ¬ ∃ (a b : V) (p : G.Walk a b), IsAugmentingPath G M p := by
  rintro ⟨a, b, p, hp⟩
  have hle := hmax (flipAlong M p) (flipAlong_isMatching hp)
  have heq := flipAlong_card hp
  omega

/-- A matching saturates precisely twice as many vertices as it has edges. -/
theorem saturated_card (hM : IsMatching G M) :
    Nat.card {v : V | Saturated M v} = 2 * Nat.card M := by
  classical
  let := Fintype.ofFinite V
  let E := M.toFinite.toFinset
  have hsat : {v : V | Saturated M v} =
      (E.biUnion Sym2.toFinset : Set V) := by
    ext v
    simp [E, Saturated, Specs.FiniteCombinatorics.Graph.Matching.Foundations.SaturatedValue]
  have hd : (E : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    exact hne (hM.2 e (by simpa [E] using he) f (by simpa [E] using hf) v
      (Sym2.mem_toFinset.mp hve) (Sym2.mem_toFinset.mp hvf))
  rw [hsat, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_biUnion hd]
  have hc : ∀ e ∈ E, e.toFinset.card = 2 := by
    intro e he
    exact Sym2.card_toFinset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeSet (hM.1 (by simpa [E] using he)))
  rw [Finset.sum_const_nat hc]
  simp [E, Nat.mul_comm]

/-- A larger matching saturates some vertex left free by the smaller matching. -/
theorem exists_saturated_not_saturated {N : Set (Sym2 V)}
    (hM : IsMatching G M) (hN : IsMatching G N) (hlt : Nat.card M < Nat.card N) :
    ∃ a, Saturated N a ∧ ¬ Saturated M a := by
  by_contra! hn
  have hsub : {v : V | Saturated N v} ⊆ {v : V | Saturated M v} := hn
  have hc := Set.ncard_le_ncard hsub
  have hm := saturated_card hM
  have hn := saturated_card hN
  change Nat.card {v : V | Saturated N v} ≤ Nat.card {v : V | Saturated M v} at hc
  omega

/-- Reversing an augmenting path preserves its defining conditions. -/
theorem augmenting_reverse (h : IsAugmentingPath G M p) :
    IsAugmentingPath G M p.reverse := by
  have ho := augmenting_length_odd h
  refine ⟨h.1, h.2.1.reverse, by simpa using h.2.2.1,
    h.2.2.2.2.1, h.2.2.2.1, ?_, ?_⟩
  · intro i hi
    simp only [SimpleGraph.Walk.length_reverse] at hi
    rw [SimpleGraph.Walk.getVert_reverse, SimpleGraph.Walk.getVert_reverse,
      Sym2.eq_swap]
    have hj : p.length - (i + 1) < p.length := by omega
    have he : p.length - (i + 1) + 1 = p.length - i := by omega
    have hh := h.2.2.2.2.2.1 (p.length - (i + 1)) hj
    rw [he] at hh
    exact hh.trans (by omega)
  · simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.getVert_reverse]
    have he : p.length - (p.length - 1) = 1 := by omega
    rw [he, Sym2.eq_swap]
    have hh := h.2.2.2.2.2.1 0 h.2.2.1
    simpa using hh

/-- The last-edge condition follows from odd length and indexed alternation. -/
private theorem augmenting_of_odd_length (hM : IsMatching G M) (hp : p.IsPath)
    (hlen : 0 < p.length) (ha : ¬ Saturated M a) (hb : ¬ Saturated M b)
    (halt : ∀ i < p.length, s(p.getVert i, p.getVert (i + 1)) ∈ M ↔ i % 2 = 1)
    (hodd : p.length % 2 = 1) : IsAugmentingPath G M p := by
  refine ⟨hM, hp, hlen, ha, hb, halt, ?_⟩
  have hh := halt (p.length - 1) (by omega)
  rw [show p.length - 1 + 1 = p.length by omega, p.getVert_length] at hh
  exact fun hm => by have := hh.mp hm; omega

/-- The graph on the same vertex type with two vertices isolated. -/
private def avoidVertices (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ≠ a ∧ y ≠ a ∧ x ≠ b ∧ y ≠ b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

omit [Finite V] in
private theorem avoidVertices_le (G : SimpleGraph V) (a b : V) :
    avoidVertices G a b ≤ G := fun _ _ h => h.1

omit [Finite V] in
private theorem avoidVertices_walk_support {x y v : V}
    (p : (avoidVertices G a b).Walk x y) (hpos : 0 < p.length) (hv : v ∈ p.support) :
    v ≠ a ∧ v ≠ b := by
  obtain ⟨e, he, hve⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
      (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpos)).mp hv
  have heG := p.edges_subset_edgeSet he
  induction e using Sym2.ind with
  | _ u w =>
    change G.Adj u w ∧ u ≠ a ∧ w ≠ a ∧ u ≠ b ∧ w ≠ b at heG
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact ⟨heG.2.1, heG.2.2.2.1⟩
    · exact ⟨heG.2.2.1, heG.2.2.2.2⟩

/-- Restore a deleted nonmatching edge and its incident matching edge. -/
private theorem restore_deleted_pair {c x y : V}
    (hM : IsMatching G M) (ha : ¬ Saturated M a) (hab : G.Adj a b)
    (hbc : s(b, c) ∈ M)
    (p : (avoidVertices G a b).Walk x y)
    (hp : IsAugmentingPath (avoidVertices G a b) (M \ {s(b, c)}) p) :
    ∃ (u v : V) (q : G.Walk u v), IsAugmentingPath G M q := by
  have hxy : x ≠ y := fun heq =>
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hp.2.2.1)
      (hp.2.1.nil_iff_eq.mpr heq)
  suffices horient : ∀ {x y : V} (p : (avoidVertices G a b).Walk x y),
      IsAugmentingPath (avoidVertices G a b) (M \ {s(b, c)}) p → y ≠ c →
        ∃ (u v : V) (q : G.Walk u v), IsAugmentingPath G M q by
    by_cases hy : y = c
    · exact horient p.reverse (augmenting_reverse hp) (by simpa [hy] using hxy)
    · exact horient p hp hy
  intro x y p hp hy
  let q := p.mapLe (avoidVertices_le G a b)
  have hqpath : q.IsPath := hp.2.1.mapLe _
  have hqlen : q.length = p.length := p.length_mapLe _
  have hqvert : ∀ i, q.getVert i = p.getVert i := by
    intro i
    exact SimpleGraph.Walk.getVert_map _ _ _
  have havoid : ∀ v ∈ q.support, v ≠ a ∧ v ≠ b := by
    intro v hv
    apply avoidVertices_walk_support p hp.2.2.1
    simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using hv
  have hmem : ∀ i, s(q.getVert i, q.getVert (i + 1)) ∈ M ↔
      s(q.getVert i, q.getVert (i + 1)) ∈ M \ {s(b, c)} := by
    intro i
    constructor
    · intro he
      refine ⟨he, ?_⟩
      intro hh
      have heq : s(q.getVert i, q.getVert (i + 1)) = s(b, c) := hh
      have hbmem : b ∈ s(q.getVert i, q.getVert (i + 1)) := by
        rw [heq]; exact Sym2.mem_mk_left _ _
      rcases Sym2.mem_iff.mp hbmem with hb | hb
      · exact (havoid _ (q.getVert_mem_support i)).2 hb.symm
      · exact (havoid _ (q.getVert_mem_support (i + 1))).2 hb.symm
    · exact fun he => he.1
  have halt : ∀ i < q.length,
      s(q.getVert i, q.getVert (i + 1)) ∈ M ↔ i % 2 = 1 := by
    intro i hi
    rw [hmem, hqvert, hqvert]
    exact hp.2.2.2.2.2.1 i (by simpa [hqlen] using hi)
  have hfree : ∀ v, v ≠ b → v ≠ c → ¬ Saturated (M \ {s(b, c)}) v →
      ¬ Saturated M v := by
    intro v hvb hvc hv ⟨e, he, hve⟩
    apply hv
    refine ⟨e, ⟨he, ?_⟩, hve⟩
    intro hh
    have heq : e = s(b, c) := hh
    rw [heq] at hve
    exact (Sym2.mem_iff.mp hve).elim hvb hvc
  have hyfree : ¬ Saturated M y :=
    hfree y (havoid y q.end_mem_support).2 hy hp.2.2.2.2.1
  by_cases hx : x = c
  · subst x
    have habout : s(a, b) ∉ M := fun he => ha ⟨_, he, Sym2.mem_mk_left _ _⟩
    have hadjbc : G.Adj b c := hM.1 hbc
    let r := (q.cons hadjbc).cons hab
    have hrpath : r.IsPath := by
      apply (hqpath.cons (havoid b · |>.2 rfl)).cons
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
      exact ⟨hab.ne, fun hh => (havoid a hh).1 rfl⟩
    have hrlen : r.length = q.length + 2 := by simp [r]
    have hralt : ∀ i < r.length,
        s(r.getVert i, r.getVert (i + 1)) ∈ M ↔ i % 2 = 1 := by
      intro i hi
      rcases i with _ | i
      · simpa [r] using habout
      rcases i with _ | i
      · simpa [r] using hbc
      · have hh := halt i (by rw [hrlen] at hi; omega)
        simpa only [r, SimpleGraph.Walk.getVert_cons_succ,
          show (i + 1 + 1) % 2 = i % 2 by omega] using hh
    exact ⟨a, y, r, augmenting_of_odd_length hM hrpath (by omega) ha hyfree
      hralt (by rw [hrlen, hqlen]; have := augmenting_length_odd hp; omega)⟩
  · exact ⟨x, y, q, augmenting_of_odd_length hM hqpath (by rw [hqlen]; exact hp.2.2.1)
      (hfree x (havoid x q.start_mem_support).2 hx hp.2.2.2.1) hyfree halt
      (by rw [hqlen]; exact augmenting_length_odd hp)⟩

private theorem matching_subset {Q : Set (Sym2 V)} (hM : IsMatching G M)
    (hQ : Q ⊆ M) : IsMatching G Q :=
  ⟨hQ.trans hM.1, fun e he f hf => hM.2 e (hQ he) f (hQ hf)⟩

/-- Removing its unique incident edge leaves a vertex unmatched. -/
private theorem matching_remove_edge_free {e : Sym2 V} {v : V}
    (hM : IsMatching G M) (he : e ∈ M) (hv : v ∈ e) :
    ¬ Saturated (M \ {e}) v := by
  rintro ⟨f, hf, hvf⟩
  exact hf.2 (hM.2 f hf.1 e he v hvf hv)

private theorem matching_avoid_vertices (hM : IsMatching G M)
    (ha : ¬ Saturated M a) (hb : ¬ Saturated M b) :
    IsMatching (avoidVertices G a b) M := by
  refine ⟨?_, hM.2⟩
  intro e he
  have hav : ∀ v ∈ e, v ≠ a ∧ v ≠ b := by
    intro v hv
    exact ⟨fun hh => ha ⟨e, he, hh ▸ hv⟩, fun hh => hb ⟨e, he, hh ▸ hv⟩⟩
  induction e using Sym2.ind with
  | _ u v =>
    exact ⟨hM.1 he, (hav u (Sym2.mem_mk_left _ _)).1,
      (hav v (Sym2.mem_mk_right _ _)).1, (hav u (Sym2.mem_mk_left _ _)).2,
      (hav v (Sym2.mem_mk_right _ _)).2⟩

/-- Induction deletes one edge of each matching and isolates its two N-endpoints. -/
private theorem larger_matching_augmenting_aux (n : ℕ) :
    ∀ (G : SimpleGraph V) (M N : Set (Sym2 V)), Nat.card N = n →
      IsMatching G M → IsMatching G N → Nat.card M < Nat.card N →
        ∃ (a b : V) (p : G.Walk a b), IsAugmentingPath G M p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G M N hn hM hN hlt
    obtain ⟨a, haN, haM⟩ := exists_saturated_not_saturated hM hN hlt
    obtain ⟨b, habN⟩ := (saturated_iff_neighbor N a).mp haN
    have hab : G.Adj a b := hN.1 habN
    have habout : s(a, b) ∉ M := fun he => haM ⟨_, he, Sym2.mem_mk_left _ _⟩
    by_cases hbM : Saturated M b
    · obtain ⟨c, hbcM⟩ := (saturated_iff_neighbor M b).mp hbM
      let M' := M \ {s(b, c)}
      let N' := N \ {s(a, b)}
      have hM' : IsMatching (avoidVertices G a b) M' := by
        apply matching_avoid_vertices (matching_subset hM Set.sdiff_subset)
        · rintro ⟨e, he, hve⟩
          exact haM ⟨e, he.1, hve⟩
        · exact matching_remove_edge_free hM hbcM (Sym2.mem_mk_left _ _)
      have hN' : IsMatching (avoidVertices G a b) N' :=
        matching_avoid_vertices (matching_subset hN Set.sdiff_subset)
          (matching_remove_edge_free hN habN (Sym2.mem_mk_left _ _))
          (matching_remove_edge_free hN habN (Sym2.mem_mk_right _ _))
      have hcM : Nat.card M' + 1 = Nat.card M :=
        Set.ncard_sdiff_singleton_add_one hbcM
      have hcN : Nat.card N' + 1 = Nat.card N :=
        Set.ncard_sdiff_singleton_add_one habN
      have hn' : Nat.card N' < n := by omega
      obtain ⟨x, y, p, hp⟩ := ih (Nat.card N') hn' (avoidVertices G a b) M' N'
        rfl hM' hN' (by omega)
      exact restore_deleted_pair hM haM hab hbcM p hp
    · refine ⟨a, b, hab.toWalk, augmenting_of_odd_length hM hab.isPath_toWalk
        (by simp) haM hbM ?_ (by simp)⟩
      intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst i
      simpa using habout

/-- Every strictly larger matching supplies an actual simple augmenting path. -/
theorem larger_matching_augmenting :
    Specs.FiniteCombinatorics.Graph.Matching.Berge.larger_matching_augmentingType := by
  intro V _ G M N hM hN hlt
  exact larger_matching_augmenting_aux (Nat.card N) G M N rfl hM hN hlt

/-- Assemble the criterion from the larger-matching construction. -/
theorem berge_criterion_of_larger_matching_augmenting
    (hlarge : Specs.FiniteCombinatorics.Graph.Matching.Berge.larger_matching_augmentingType.{u}) :
    Specs.FiniteCombinatorics.Graph.Matching.Berge.berge_criterionType.{u} := by
  intro V _ G M hM
  constructor
  · exact maximum_has_no_augmenting_path hM
  · intro hnone N hN
    by_contra hle
    have hlt : Nat.card M < Nat.card N := Nat.lt_of_not_ge hle
    exact hnone (hlarge G M N hM hN hlt)

/-- Berge's criterion for arbitrary finite simple graphs. -/
theorem berge_criterion :
    Specs.FiniteCombinatorics.Graph.Matching.Berge.berge_criterionType :=
  berge_criterion_of_larger_matching_augmenting larger_matching_augmenting

end FiniteCombinatorics.Graph.Matching
