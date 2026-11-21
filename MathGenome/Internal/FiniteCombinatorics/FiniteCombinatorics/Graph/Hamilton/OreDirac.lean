import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Euler.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Hamilton.OreDirac

/-! Ore's theorem and Dirac's corollary (paper.tex W40). The proof closes a
longest path using endpoint degree counts, then extends at an outside neighbor
to show the resulting cycle spans every vertex. -/

universe u
noncomputable section
namespace FiniteCombinatorics.Graph
open SimpleGraph

section Helpers
variable {V : Type u} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
/-- A neighbor of an endpoint of a longest path is already on the path. -/
lemma longestPath_neighbor_mem {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {v : V} (hv : G.Adj a v) : v ∈ p.support := by
  by_contra hn
  have hh := hmax v b (.cons hv.symm p) (hp.cons hn)
  simp only [Walk.length_cons] at hh
  omega

/-- The degree-sum condition already implies that any two vertices are reachable. -/
lemma ore_preconnected [DecidableRel G.Adj]
    (h : ∀ a b : V, a ≠ b → ¬ G.Adj a b →
      Fintype.card V ≤ G.degree a + G.degree b) : G.Preconnected := by
  classical
  intro a b
  by_cases hab : a = b
  · subst b; exact .rfl
  by_cases he : G.Adj a b
  · exact he.reachable
  have hs := h a b hab he
  have hc : (G.neighborFinset a ∪ G.neighborFinset b).card < Fintype.card V :=
    Finset.card_lt_univ_of_notMem (x := a) (by simp [show ¬ G.Adj b a from fun h => he h.symm])
  have hi : (G.neighborFinset a ∩ G.neighborFinset b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hh := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
    simp only [hempty, Finset.card_empty, Nat.add_zero, G.card_neighborFinset_eq_degree] at hh
    omega
  obtain ⟨c, hc⟩ := hi
  simp only [Finset.mem_inter, mem_neighborFinset] at hc
  exact hc.1.reachable.trans hc.2.symm.reachable

/-- A connected graph on at least three vertices has a path with two edges. -/
lemma exists_two_edge_path (hn : 3 ≤ Fintype.card V) (hc : G.Preconnected) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = 2 := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 3) (β := V) (by simpa using hn)
  have hab : f 0 ≠ f 1 := f.injective.ne (by decide)
  have hac : f 0 ≠ f 2 := f.injective.ne (by decide)
  have hbc : f 1 ≠ f 2 := f.injective.ne (by decide)
  obtain ⟨q, hq⟩ := hc.exists_isPath (f 0) (f 1)
  obtain ⟨r, hr⟩ := hc.exists_isPath (f 0) (f 2)
  by_cases hq2 : 2 ≤ q.length
  · exact ⟨_, _, q.take 2, hq.take 2, by simp [Nat.min_eq_left hq2]⟩
  by_cases hr2 : 2 ≤ r.length
  · exact ⟨_, _, r.take 2, hr.take 2, by simp [Nat.min_eq_left hr2]⟩
  have hql : q.length = 1 := by
    have : q.length ≠ 0 := fun h => hab (Walk.eq_of_length_eq_zero h)
    omega
  have hrl : r.length = 1 := by
    have : r.length ≠ 0 := fun h => hac (Walk.eq_of_length_eq_zero h)
    omega
  exact ⟨f 1, f 2, .cons (Walk.adj_of_length_eq_one hql).symm
    (.cons (Walk.adj_of_length_eq_one hrl) .nil), by simp [hbc], rfl⟩

/-- The endpoint degree sum on a path forces two crossing endpoint edges. -/
lemma path_crossing_edges [DecidableRel G.Adj] {a b : V} (p : G.Walk a b)
    (hp : p.IsPath)
    (ha : ∀ v, G.Adj a v → v ∈ p.support)
    (hb : ∀ v, G.Adj b v → v ∈ p.support)
    (hs : p.length < G.degree a + G.degree b) :
    ∃ i, i < p.length ∧ G.Adj a (p.getVert (i + 1)) ∧ G.Adj (p.getVert i) b := by
  classical
  let I := (Finset.range p.length).filter (fun i => G.Adj a (p.getVert (i + 1)))
  let J := (Finset.range p.length).filter (fun i => G.Adj (p.getVert i) b)
  have hI : I.card = G.degree a := by
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun i _ => p.getVert (i + 1))
    · intro i hi
      exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      have hi' := (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      have hj' := (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
      have hh := hp.getVert_injOn (by simp; omega) (by simp; omega) hij
      omega
    · intro v hv
      have hadj := (G.mem_neighborFinset _ _).mp hv
      obtain ⟨k, hk, hkl⟩ := Walk.mem_support_iff_exists_getVert.mp (ha v hadj)
      have hk0 : k ≠ 0 := by
        intro he; subst k
        simp only [Walk.getVert_zero] at hk
        exact hadj.ne hk
      refine ⟨k - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩
      · simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0), hk] using hadj
      · simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] using hk
  have hJ : J.card = G.degree b := by
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun i _ => p.getVert i)
    · intro i hi
      exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hi).2.symm
    · intro i hi j hj hij
      exact hp.getVert_injOn
        (by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; simp; omega)
        (by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; simp; omega) hij
    · intro v hv
      have hadj := (G.mem_neighborFinset _ _).mp hv
      obtain ⟨k, hk, hkl⟩ := Walk.mem_support_iff_exists_getVert.mp (hb v hadj)
      have hkn : k ≠ p.length := by
        intro he; subst k
        simp only [Walk.getVert_length] at hk
        exact hadj.ne hk
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk ▸ hadj.symm⟩, hk⟩
  have hi : (I ∩ J).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have heq := Finset.card_union_add_card_inter I J
    have hle : (I ∪ J).card ≤ p.length := by
      calc
        _ ≤ (Finset.range p.length).card := Finset.card_le_card (by
          intro i hi
          rcases Finset.mem_union.mp hi with h | h
          · exact (Finset.mem_filter.mp h).1
          · exact (Finset.mem_filter.mp h).1)
        _ = _ := Finset.card_range _
    simp only [he, Finset.card_empty, Nat.add_zero, hI, hJ] at heq
    omega
  obtain ⟨i, hi⟩ := hi
  obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hi
  exact ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1,
    (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩

/-- Closing a path of at least two edges gives a simple cycle. -/
lemma close_path_isCycle {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hl : 2 ≤ p.length) (hba : G.Adj b a) : (p.concat hba).IsCycle := by
  apply (cycle_iff G a _).mpr
  constructor
  · simp only [Walk.length_concat]; omega
  · simpa [Walk.support_concat] using hp.support_nodup

/-- Reverse the suffix at a pair of crossing edges to close the path. -/
lemma cycle_of_crossing_edges {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hl : 2 ≤ p.length) {i : ℕ} (hi : i < p.length)
    (ha : G.Adj a (p.getVert (i + 1))) (hb : G.Adj (p.getVert i) b) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = p.length + 1 ∧
      ∀ v, v ∈ c.support ↔ v ∈ p.support := by
  let q := ((p.take i).concat hb).append (p.drop (i + 1)).reverse
  have hqs : q.support = p.support.take (i + 1) ++ (p.support.drop (i + 1)).reverse := by
    simp [q, Walk.support_append_eq_support_dropLast_append, Walk.support_concat,
      Walk.support_take, Walk.support_reverse, Nat.min_eq_left (by omega : i + 1 ≤ p.length)]
  have hperm : q.support.Perm p.support := by
    rw [hqs]
    have hh := (List.Perm.refl (p.support.take (i + 1))).append
      (List.reverse_perm (p.support.drop (i + 1)))
    simpa only [List.take_append_drop] using hh
  have hq : q.IsPath := Walk.IsPath.mk' (hperm.nodup_iff.mpr hp.support_nodup)
  have hql : q.length = p.length := by
    have hh := hperm.length_eq
    rw [Walk.length_support, Walk.length_support] at hh
    omega
  refine ⟨q.concat ha.symm, close_path_isCycle G q hq (by omega) ha.symm, ?_, ?_⟩
  · simp [hql]
  · intro v
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | rfl)
      · exact hperm.mem_iff.mp h
      · exact p.start_mem_support
    · intro h; exact Or.inl (hperm.mem_iff.mpr h)

omit [Fintype V] in
/-- A cycle whose deletion of one edge has maximal path length must span a
connected graph: an outside neighbor would extend the rotated path. -/
lemma cycle_spans_of_longest (hc : G.Preconnected) {a : V} (c : G.Walk a a)
    (hcyc : c.IsCycle)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length < c.length) :
    ∀ v, v ∈ c.support := by
  classical
  have hclosed : ∀ {x y : V}, x ∈ c.support → G.Adj x y → y ∈ c.support := by
    intro x y hx hxy
    by_contra hy
    let r := c.rotate x hx
    have hr : r.IsCycle := hcyc.rotate hx
    have hyr : y ∉ r.dropLast.support := by
      intro h
      rw [Walk.support_dropLast hr.not_nil] at h
      have hh := List.mem_of_mem_dropLast h
      exact hy ((c.mem_support_rotate_iff x hx).mp hh)
    have hq := hr.isPath_dropLast.cons (h := hxy.symm) hyr
    have hh := hmax y r.penultimate (.cons hxy.symm r.dropLast) hq
    have hl : r.dropLast.length + 1 = c.length := by
      simpa [r] using Walk.length_dropLast_add_one hr.not_nil
    simp only [Walk.length_cons] at hh
    omega
  have hwalk : ∀ {x y : V} (q : G.Walk x y), x ∈ c.support → y ∈ c.support := by
    intro x y q
    induction q with
    | nil => exact fun h => h
    | cons h q ih => exact fun hx => ih (hclosed hx h)
  intro v
  obtain ⟨q⟩ := hc a v
  exact hwalk q c.start_mem_support

end Helpers

/-- Ore's degree-sum condition for a finite simple graph, without an assumed
connectivity condition. -/
theorem ore : Specs.FiniteCombinatorics.Graph.Hamilton.OreDirac.oreType := by
  intro V _ G hn h
  classical
  let : Fintype V := Fintype.ofFinite V
  have hn' : 3 ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hn
  have hs : ∀ a b : V, a ≠ b → ¬ G.Adj a b →
      Fintype.card V ≤ G.degree a + G.degree b := by
    intro a b hab he
    have hh := h a b hab he
    simpa only [Specs.FiniteCombinatorics.Graph.Foundations.degreeValue,
      Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree] using hh
  have hc := ore_preconnected G hs
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a, b, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  obtain ⟨x, y, q, hq, hql⟩ := exists_two_edge_path G hn' hc
  have hl : 2 ≤ p.length := by have := hmax x y q hq; omega
  have ha : ∀ v, G.Adj a v → v ∈ p.support :=
    fun v hv => longestPath_neighbor_mem G p hp hmax hv
  have hb : ∀ v, G.Adj b v → v ∈ p.support := by
    intro v hv
    have hh := longestPath_neighbor_mem G p.reverse hp.reverse
      (fun x y q hq => by simpa using hmax x y q hq) hv
    simpa using hh
  have hcycle : ∃ c : G.Walk a a, c.IsCycle ∧ c.length = p.length + 1 := by
    by_cases he : G.Adj a b
    · exact ⟨p.concat he.symm, close_path_isCycle G p hp hl he.symm, by simp⟩
    · have hab : a ≠ b := by
        intro heq; subst b
        have hh := (Walk.isPath_iff_nil.mp hp).length_eq_zero
        omega
      have hdeg := hs a b hab he
      have hlen := hp.length_lt
      obtain ⟨i, hi, hia, hib⟩ := path_crossing_edges G p hp ha hb (by omega)
      obtain ⟨c, hcyc, hcl, _⟩ := cycle_of_crossing_edges G p hp hl hi hia hib
      exact ⟨c, hcyc, hcl⟩
  obtain ⟨c, hcyc, hcl⟩ := hcycle
  refine ⟨a, c, hcyc, cycle_spans_of_longest G hc c hcyc ?_⟩
  intro x y q hq
  have := hmax x y q hq
  omega

/-- Dirac's condition, in its exact integral form. -/
theorem dirac : Specs.FiniteCombinatorics.Graph.Hamilton.OreDirac.diracType := by
  intro V _ G hn h
  apply ore G hn
  intro a b _ _
  have ha := h a
  have hb := h b
  omega

end FiniteCombinatorics.Graph
