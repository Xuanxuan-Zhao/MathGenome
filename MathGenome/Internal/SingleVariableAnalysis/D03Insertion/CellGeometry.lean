import MathGenome.Internal.SingleVariableAnalysis.D03Insertion.FinitePartitionData
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.CellGeometry
import Lean.Elab.Tactic.Omega

noncomputable section

namespace D03Insertion

/-- Node membership exposes an actual index. -/
theorem mem_nodes_iff {n : ℕ} (q : Fin (n + 1) → ℝ) (x : ℝ) :
    x ∈ nodes q ↔ ∃ k, q k = x := by
  simp [nodes]

/-- No partition node lies strictly between consecutive nodes. -/
theorem no_node_inside_cell {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : StrictMono q) (i : Fin n) (k : Fin (n + 1)) :
    ¬ (left q i < q k ∧ q k < right q i) := by
  intro h
  have h₁ := hq.lt_iff_lt.mp h.1
  have h₂ := hq.lt_iff_lt.mp h.2
  have : i.castSucc.val < k.val := h₁
  have : k.val < i.succ.val := h₂
  simp only [Fin.val_castSucc, Fin.val_succ] at *
  omega

/-- Cells in a strictly ordered partition have disjoint open interiors.
Consequently a positive-length interval is contained in at most one cell. -/
theorem containing_cell_unique {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : StrictMono q) {x y : ℝ} (hxy : x < y) {i k : Fin n}
    (hi : left q i ≤ x ∧ y ≤ right q i)
    (hk : left q k ≤ x ∧ y ≤ right q k) : i = k := by
  apply le_antisymm
  · by_contra h
    have hki : k < i := lt_of_not_ge h
    have hstep : k.succ ≤ i.castSucc := by
      change k.val + 1 ≤ i.val
      exact hki
    have hsep : right q k ≤ left q i := hq.monotone hstep
    exact (not_le_of_gt hxy) (hk.2.trans (hsep.trans hi.1))
  · by_contra h
    have hik : i < k := lt_of_not_ge h
    have hstep : i.succ ≤ k.castSucc := by
      change i.val + 1 ≤ k.val
      exact hik
    have hsep : right q i ≤ left q k := hq.monotone hstep
    exact (not_le_of_gt hxy) (hi.2.trans (hsep.trans hk.1))

/-- The old half-open cells cover [a,b). The proof takes the last node ≤ x. -/
theorem exists_halfopen_cell {a b x : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : ValidPartition a b q) (hax : a ≤ x) (hxb : x < b) :
    ∃ i : Fin n, left q i ≤ x ∧ x < right q i := by
  classical
  let A := Finset.univ.filter (fun k : Fin (n + 1) => q k ≤ x)
  have hA : A.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [hq.2.2.1] using hax
  let k := A.max' hA
  have hk : q k ≤ x := (Finset.mem_filter.mp (A.max'_mem hA)).2
  have hklast : k < Fin.last n := by
    apply hq.2.1.lt_iff_lt.mp
    rw [hq.2.2.2]
    exact hk.trans_lt hxb
  let i : Fin n := ⟨k.val, hklast⟩
  have hik : i.castSucc = k := Fin.ext rfl
  refine ⟨i, ?_, ?_⟩
  · simpa only [left, hik] using hk
  · by_contra h
    have hnext : i.succ ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_of_not_gt h
    have hle : i.succ ≤ k := A.le_max' _ hnext
    have hlt : k < i.succ := by
      rw [← hik]
      exact i.castSucc_lt_succ
    exact (not_le_of_gt hlt) hle

/-- A node other than the final node starts a cell. -/
theorem node_starts_cell {a b x : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : ValidPartition a b q) (hx : x ∈ nodes q) (hxb : x < b) :
    ∃ i : Fin n, left q i = x := by
  obtain ⟨k, hk⟩ := (mem_nodes_iff q x).mp hx
  have hkn : k < Fin.last n := hq.2.1.lt_iff_lt.mp (by simpa only [hk, hq.2.2.2] using hxb)
  let i : Fin n := ⟨k.val, hkn⟩
  exact ⟨i, hk⟩

/-- A node other than the initial node ends a cell. -/
theorem node_ends_cell {a b x : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : ValidPartition a b q) (hx : x ∈ nodes q) (hax : a < x) :
    ∃ i : Fin n, right q i = x := by
  obtain ⟨k, hk⟩ := (mem_nodes_iff q x).mp hx
  have hkpos : (0 : Fin (n + 1)) < k := hq.2.1.lt_iff_lt.mp (by simpa only [hk, hq.2.2.1] using hax)
  let i : Fin n := ⟨k.val - 1, by have := k.isLt; change 0 < k.val at hkpos; omega⟩
  have hik : i.succ = k := by
    apply Fin.ext
    change k.val - 1 + 1 = k.val
    change 0 < k.val at hkpos
    omega
  exact ⟨i, by simpa only [right, hik] using hk⟩

/-- If x is a partition node to the right of a cell's left endpoint, its
right endpoint is at most x. -/
theorem right_le_node {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : StrictMono q) (i : Fin n) {x : ℝ} (hx : x ∈ nodes q)
    (hix : left q i < x) : right q i ≤ x := by
  obtain ⟨k, rfl⟩ := (mem_nodes_iff q x).mp hx
  have hik := hq.lt_iff_lt.mp hix
  apply hq.monotone
  change i.val + 1 ≤ k.val
  exact hik

/-- The symmetric endpoint bound for a node left of the right endpoint. -/
theorem node_le_left {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : StrictMono q) (i : Fin n) {x : ℝ} (hx : x ∈ nodes q)
    (hxi : x < right q i) : x ≤ left q i := by
  obtain ⟨k, rfl⟩ := (mem_nodes_iff q x).mp hx
  have hki := hq.lt_iff_lt.mp hxi
  apply hq.monotone
  change k.val ≤ i.val
  change k.val < i.val + 1 at hki
  omega

/-- Every cell in a refinement has a unique old parent. Only inclusion of the
old nodes, not a chosen sorting construction, is needed. -/
theorem cell_parent_of_nodes_subset {a b : ℝ} {n t : ℕ}
    {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ}
    (hq : ValidPartition a b q) (hr : ValidPartition a b r)
    (hsub : nodes q ⊆ nodes r) (j : Fin t) :
    ∃! i : Fin n, left q i ≤ left r j ∧ right r j ≤ right q i := by
  have hleft : a ≤ left r j := by
    rw [← hr.2.2.1]
    exact hr.2.1.monotone (Fin.zero_le _)
  have hright : left r j < b := by
    rw [← hr.2.2.2]
    apply hr.2.1
    exact j.isLt
  obtain ⟨i, hi⟩ := exists_halfopen_cell hq hleft hright
  have hinode : right q i ∈ nodes r := hsub ((mem_nodes_iff q _).mpr ⟨i.succ, rfl⟩)
  have hij : right r j ≤ right q i := right_le_node hr.2.1 j hinode hi.2
  refine ⟨i, ⟨hi.1, hij⟩, ?_⟩
  intro k hk
  exact containing_cell_unique hq.2.1 (sub_pos.mp (width_pos hr j)) hk ⟨hi.1, hij⟩

theorem refined_cell_parent : Specification.refined_cell_parentType := by
  intro a b hab s n t p q r hp hq hr hu j
  apply cell_parent_of_nodes_subset hq hr _ j
  rw [hu]
  exact Finset.subset_union_right


/-- Every cell lies in the original closed interval. -/
theorem cell_endpoint_bounds {a b : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : ValidPartition a b q) (i : Fin n) :
    a ≤ left q i ∧ right q i ≤ b := by
  constructor
  · rw [← hq.2.2.1]
    exact hq.2.1.monotone (Fin.zero_le _)
  · rw [← hq.2.2.2]
    exact hq.2.1.monotone (Fin.le_last _)

/-- The left endpoint of any cell precedes the final endpoint. -/
theorem cell_left_lt_end {a b : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : ValidPartition a b q) (i : Fin n) : left q i < b := by
  rw [← hq.2.2.2]
  exact hq.2.1 i.isLt

/-- The right endpoint of any cell follows the initial endpoint. -/
theorem start_lt_cell_right {a b : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : ValidPartition a b q) (i : Fin n) : a < right q i := by
  rw [← hq.2.2.1]
  apply hq.2.1
  change 0 < i.val + 1
  omega

/-- Under the exact node-union hypothesis, an old cell is unmarked precisely
when no refined node lies in its open interior. -/
theorem unmarked_iff_no_refined_node {a b : ℝ} {s n t : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ}
    (hp : ValidPartition a b p) (hq : ValidPartition a b q)
    (hu : nodes r = nodes p ∪ nodes q) (i : Fin n) :
    i ∉ marked p q ↔ ∀ k, ¬ (left q i < r k ∧ r k < right q i) := by
  classical
  constructor
  · intro hi k hk
    have hkNode : r k ∈ nodes p ∪ nodes q := by
      rw [← hu]
      exact (mem_nodes_iff r _).mpr ⟨k, rfl⟩
    rcases Finset.mem_union.mp hkNode with hkP | hkQ
    · obtain ⟨l, hl⟩ := (mem_nodes_iff p _).mp hkP
      have hpl : a < p l := by
        rw [hl]
        exact (cell_endpoint_bounds hq i).1.trans_lt hk.1
      have hlp : p l < b := by
        rw [hl]
        exact hk.2.trans_le (cell_endpoint_bounds hq i).2
      have h0 : (0 : Fin (s + 1)) < l := hp.2.1.lt_iff_lt.mp (by
        simpa only [hp.2.2.1] using hpl)
      have hs : l < Fin.last s := hp.2.1.lt_iff_lt.mp (by
        simpa only [hp.2.2.2] using hlp)
      apply hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, l, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, h0, hs⟩
      · simpa only [hl] using hk
    · obtain ⟨l, hl⟩ := (mem_nodes_iff q _).mp hkQ
      exact no_node_inside_cell hq.2.1 i l (by simpa only [hl] using hk)
  · intro hno hi
    obtain ⟨l, hl, hli⟩ := (Finset.mem_filter.mp hi).2
    have hnode : p l ∈ nodes r := by
      rw [hu]
      exact Finset.mem_union_left _ ((mem_nodes_iff p _).mpr ⟨l, rfl⟩)
    obtain ⟨k, hk⟩ := (mem_nodes_iff r _).mp hnode
    exact hno k (by simpa only [hk] using hli)

/-- Each old cell has a refined cell starting at its left endpoint, contained
in that old cell. This holds whether or not the old cell is split. -/
theorem refined_cell_at_left {a b : ℝ} {n t : ℕ}
    {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ}
    (hq : ValidPartition a b q) (hr : ValidPartition a b r)
    (hsub : nodes q ⊆ nodes r) (i : Fin n) :
    ∃ j, left r j = left q i ∧ right r j ≤ right q i := by
  have hnode : left q i ∈ nodes r :=
    hsub ((mem_nodes_iff q _).mpr ⟨i.castSucc, rfl⟩)
  obtain ⟨j, hj⟩ := node_starts_cell hr hnode (cell_left_lt_end hq i)
  refine ⟨j, hj, right_le_node hr.2.1 j ?_ ?_⟩
  · exact hsub ((mem_nodes_iff q _).mpr ⟨i.succ, rfl⟩)
  · rw [hj]
    exact sub_pos.mp (width_pos hq i)

/-- The corresponding refined cell at the right endpoint. -/
theorem refined_cell_at_right {a b : ℝ} {n t : ℕ}
    {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ}
    (hq : ValidPartition a b q) (hr : ValidPartition a b r)
    (hsub : nodes q ⊆ nodes r) (i : Fin n) :
    ∃ j, right r j = right q i ∧ left q i ≤ left r j := by
  have hnode : right q i ∈ nodes r :=
    hsub ((mem_nodes_iff q _).mpr ⟨i.succ, rfl⟩)
  obtain ⟨j, hj⟩ := node_ends_cell hr hnode (start_lt_cell_right hq i)
  refine ⟨j, hj, node_le_left hr.2.1 j ?_ ?_⟩
  · exact hsub ((mem_nodes_iff q _).mpr ⟨i.castSucc, rfl⟩)
  · rw [hj]
    exact sub_pos.mp (width_pos hq i)

/-- Absence of inserted interior nodes makes the old cell exactly one refined cell. -/
theorem unmarked_cell_exists_unique {a b : ℝ} {s n t : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ}
    (hp : ValidPartition a b p) (hq : ValidPartition a b q)
    (hr : ValidPartition a b r) (hu : nodes r = nodes p ∪ nodes q)
    (i : Fin n) (hi : i ∉ marked p q) :
    ∃! j, left r j = left q i ∧ right r j = right q i := by
  have hsub : nodes q ⊆ nodes r := by
    rw [hu]
    exact Finset.subset_union_right
  obtain ⟨j, hjL, hjR⟩ := refined_cell_at_left hq hr hsub i
  have heq : right r j = right q i := by
    apply le_antisymm hjR
    by_contra h
    have hlt : right r j < right q i := lt_of_not_ge h
    have hpos : left q i < right r j := by
      rw [← hjL]
      exact sub_pos.mp (width_pos hr j)
    exact (unmarked_iff_no_refined_node hp hq hu i).mp hi j.succ ⟨hpos, hlt⟩
  refine ⟨j, ⟨hjL, heq⟩, ?_⟩
  intro k hk
  apply Fin.castSucc_injective
  apply hr.2.1.injective
  exact hk.1.trans hjL.symm

/-- Matching endpoints imply unmarkedness: any inserted interior node would
lie strictly between two consecutive refined nodes. -/
theorem matching_cell_unmarked {a b : ℝ} {s n t : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ}
    (hp : ValidPartition a b p) (hq : ValidPartition a b q)
    (hr : ValidPartition a b r) (hu : nodes r = nodes p ∪ nodes q)
    {i : Fin n} {j : Fin t}
    (hj : left r j = left q i ∧ right r j = right q i) : i ∉ marked p q := by
  apply (unmarked_iff_no_refined_node hp hq hu i).mpr
  intro k hk
  apply no_node_inside_cell hr.2.1 j k
  simpa only [hj.1, hj.2] using hk

/-- For every parent assignment satisfying containment, a fiber is a singleton
exactly when that refined cell has the old endpoints (and so is unmarked). -/
theorem singleton_parent_fiber_iff {a b : ℝ} {s n t : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ}
    (hp : ValidPartition a b p) (hq : ValidPartition a b q)
    (hr : ValidPartition a b r) (hu : nodes r = nodes p ∪ nodes q)
    (c : Fin t → Fin n)
    (hc : ∀ j, left q (c j) ≤ left r j ∧ right r j ≤ right q (c j))
    (i : Fin n) (j : Fin t) :
    (∀ k, c k = i ↔ k = j) ↔
      ((left r j = left q i ∧ right r j = right q i) ∧ i ∉ marked p q) := by
  have hsub : nodes q ⊆ nodes r := by
    rw [hu]
    exact Finset.subset_union_right
  have hparent : ∀ k, left q i ≤ left r k ∧ right r k ≤ right q i → c k = i := by
    intro k hk
    exact containing_cell_unique hq.2.1 (sub_pos.mp (width_pos hr k)) (hc k) hk
  constructor
  · intro hsingle
    obtain ⟨kL, hleft, hright_le⟩ := refined_cell_at_left hq hr hsub i
    have hL : kL = j := (hsingle kL).mp (hparent kL ⟨hleft.ge, hright_le⟩)
    obtain ⟨kR, hright, hleft_le⟩ := refined_cell_at_right hq hr hsub i
    have hR : kR = j := (hsingle kR).mp (hparent kR ⟨hleft_le, hright.le⟩)
    have hj : left r j = left q i ∧ right r j = right q i := by
      exact ⟨hL ▸ hleft, hR ▸ hright⟩
    exact ⟨hj, matching_cell_unmarked hp hq hr hu hj⟩
  · rintro ⟨hj, _⟩ k
    constructor
    · intro hk
      have hinside : left r j ≤ left r k ∧ right r k ≤ right r j := by
        simpa only [hk, hj.1, hj.2] using hc k
      exact containing_cell_unique hr.2.1 (sub_pos.mp (width_pos hr k))
        ⟨le_rfl, le_rfl⟩ hinside
    · intro hk
      rw [hk]
      exact hparent j ⟨hj.1.ge, hj.2.le⟩

/-- Complete cell geometry for any valid enumeration of the exact node union. -/
theorem refined_cell_geometry : Specification.refined_cell_geometryType := by
  classical
  intro a b hab s n t p q r hp hq hr hu
  have hparents := refined_cell_parent hab hp hq hr hu
  let c : Fin t → Fin n := fun j => Classical.choose (hparents j)
  have hc : ∀ j, left q (c j) ≤ left r j ∧ right r j ≤ right q (c j) :=
    fun j => (Classical.choose_spec (hparents j)).1
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · intro j i hi
    exact ((Classical.choose_spec (hparents j)).2 i hi).symm
  · exact fun i hi => unmarked_cell_exists_unique hp hq hr hu i hi
  · exact singleton_parent_fiber_iff hp hq hr hu c hc

end D03Insertion
