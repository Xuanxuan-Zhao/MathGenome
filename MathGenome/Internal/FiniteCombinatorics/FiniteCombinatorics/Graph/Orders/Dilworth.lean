import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Orders.Dilworth
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.Konig
import Mathlib.Order.Iterate
import Mathlib.Data.Fintype.Order

universe u
noncomputable section
open scoped Classical
namespace FiniteCombinatorics.Graph.Orders

abbrev IsChainPartition :
    Specs.FiniteCombinatorics.Graph.Orders.Dilworth.IsChainPartitionType :=
  Specs.FiniteCombinatorics.Graph.Orders.Dilworth.IsChainPartitionValue

abbrev width : Specs.FiniteCombinatorics.Graph.Orders.Dilworth.widthType :=
  Specs.FiniteCombinatorics.Graph.Orders.Dilworth.widthValue

variable {P : Type u} [Fintype P] [PartialOrder P]

/-- A chain part contains at most one member of any antichain. -/
lemma antichain_le_partition (p : Finpartition (Finset.univ : Finset P))
    (hp : IsChainPartition p) (a : Finset P)
    (ha : IsAntichain (· ≤ ·) (a : Set P)) : a.card ≤ p.parts.card := by
  classical
  let f : a → p.parts := fun x => ⟨p.part x, p.part_mem.mpr (Finset.mem_univ _)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hparts : p.part x.val = p.part y.val := congrArg Subtype.val hxy
    have hx : x.val ∈ p.part x.val := p.mem_part (Finset.mem_univ _)
    have hy : y.val ∈ p.part x.val := hparts ▸ p.mem_part (Finset.mem_univ _)
    by_contra hne
    rcases hp _ (p.part_mem.mpr (Finset.mem_univ _)) hx hy hne with h | h
    · exact ha x.property y.property hne h
    · exact ha y.property x.property (Ne.symm hne) h
  simpa using Fintype.card_le_of_injective f hf

/-- A finite system of strictly increasing arrows with unique successors admits
a chain partition with at most as many parts as sources. -/
lemma chain_partition_of_arrows (r : P → P → Prop)
    (hlt : ∀ {x y}, r x y → x < y)
    (hout : ∀ {x y z}, r x y → r x z → y = z) :
    ∃ p : Finpartition (Finset.univ : Finset P), IsChainPartition p ∧
      p.parts.card ≤ (Finset.univ.filter (fun y => ¬ ∃ x, r x y)).card := by
  classical
  let f : P → P := fun x => if h : ∃ y, r x y then h.choose else x
  have hf : ∀ {x y}, r x y → f x = y := by
    intro x y hxy
    dsimp [f]
    split_ifs with h
    · exact hout h.choose_spec hxy
    · exact (h ⟨y, hxy⟩).elim
  have hinc : id ≤ f := by
    intro x
    dsimp [f]
    split_ifs with h
    · exact (hlt h.choose_spec).le
    · exact le_rfl
  have horigin : ∀ x : P, ∃ z, (¬ ∃ y, r y z) ∧ ∃ n : ℕ, f^[n] z = x := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x ih =>
      by_cases h : ∃ y, r y x
      · obtain ⟨y, hy⟩ := h
        obtain ⟨z, hz, n, hn⟩ := ih y (hlt hy)
        exact ⟨z, hz, n + 1, by rw [Function.iterate_succ_apply', hn, hf hy]⟩
      · exact ⟨x, h, 0, rfl⟩
  let sources := Finset.univ.filter (fun y => ¬ ∃ x, r x y)
  let c : P → sources := fun x =>
    ⟨(horigin x).choose, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (horigin x).choose_spec.1⟩⟩
  have hc : ∀ x, ∃ n : ℕ, f^[n] (c x).val = x :=
    fun x => (horigin x).choose_spec.2
  let fiber : sources → Finset P := fun z => Finset.univ.filter (fun x => c x = z)
  let parts := (Finset.univ.image fiber).erase ∅
  have hmem : ∀ {t}, t ∈ parts ↔ t ≠ ∅ ∧ ∃ z, fiber z = t := by
    intro t
    simp [parts]
  let p : Finpartition (Finset.univ : Finset P) := Finpartition.ofExistsUnique parts
    (fun _ _ => Finset.subset_univ _) (by
      intro x _
      have hx : x ∈ fiber (c x) := by simp [fiber]
      have hempty : fiber (c x) ≠ ∅ := Finset.ne_empty_of_mem hx
      refine ⟨fiber (c x), ⟨hmem.mpr ⟨hempty, c x, rfl⟩, hx⟩, ?_⟩
      rintro t ⟨ht, hxt⟩
      obtain ⟨_, z, rfl⟩ := hmem.mp ht
      have hz : c x = z := (Finset.mem_filter.mp hxt).2
      rw [hz]) (by simp [parts])
  refine ⟨p, ?_, ?_⟩
  · intro t ht x hx y hy _
    obtain ⟨_, z, rfl⟩ := hmem.mp ht
    have hxz := (Finset.mem_filter.mp hx).2
    have hyz := (Finset.mem_filter.mp hy).2
    obtain ⟨n, hn⟩ := hc x
    obtain ⟨m, hm⟩ := hc y
    rw [hxz] at hn
    rw [hyz] at hm
    rcases le_total n m with h | h
    · exact Or.inl (hn ▸ hm ▸ Function.monotone_iterate_of_id_le hinc h z.val)
    · exact Or.inr (hm ▸ hn ▸ Function.monotone_iterate_of_id_le hinc h z.val)
  · exact Finset.card_erase_le.trans
      ((Finset.card_image_le).trans (by simp [sources]))

/-- Left-to-right adjacency records strict comparability in the poset. -/
def strictOrderBipartite (P : Type u) [PartialOrder P] : SimpleGraph (P ⊕ P) where
  Adj a b := match a, b with
    | .inl x, .inr y => x < y
    | .inr y, .inl x => x < y
    | _, _ => False
  symm := ⟨by rintro (x | x) (y | y) h <;> exact h⟩
  loopless := ⟨by rintro (x | x) h <;> exact h⟩

omit [Fintype P] in
lemma strictOrderBipartite_bipartition :
    Matching.Alternating.Bipartition (strictOrderBipartite P)
      {v | v.isLeft} {v | v.isRight} where
  disjoint := by
    rw [Set.disjoint_left]
    rintro (x | x) hx hy <;> simp_all
  cover := by
    ext v
    cases v <;> simp
  crosses := by
    rintro (x | x) (y | y) h
    · exact h.elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact h.elim

/-- The matching and cover provide a chain partition and an antichain of the
same size. Neither maximum width nor minimum chain count is assumed. -/
lemma exists_equal_chain_partition_antichain :
    ∃ (p : Finpartition (Finset.univ : Finset P)) (a : Finset P),
      IsChainPartition p ∧ IsAntichain (· ≤ ·) (a : Set P) ∧
      p.parts.card = a.card := by
  classical
  let G := strictOrderBipartite P
  obtain ⟨M, C, hM, hC, hMC, _, _⟩ :=
    Matching.konig_matching_cover G {v | v.isLeft} {v | v.isRight}
      strictOrderBipartite_bipartition
  let r : P → P → Prop := fun x y => s(Sum.inl x, Sum.inr y) ∈ M
  have hlt : ∀ {x y}, r x y → x < y := fun h => hM.1 h
  have hout : ∀ {x y z}, r x y → r x z → y = z := by
    intro x y z hxy hxz
    exact Sum.inr.inj
      (((Matching.matching_iff_neighbors G M).mp hM).2 _ _ _ hxy hxz)
  obtain ⟨p, hp, hcount⟩ := chain_partition_of_arrows r hlt hout
  let incoming := Finset.univ.filter (fun y => ∃ x, r x y)
  have hsource : (Finset.univ.filter (fun y => ¬ ∃ x, r x y)).card +
      incoming.card = Fintype.card P := by
    simpa [incoming, Nat.add_comm] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset P)) (fun y => ∃ x, r x y)
  have hend : ∀ e : M, ∃ x y : P, e.val = s(Sum.inl x, Sum.inr y) := by
    intro e
    have he := hM.1 e.property
    generalize heq : e.val = d at he ⊢
    induction d using Sym2.ind with
    | _ a b =>
      cases a with
      | inl x =>
        cases b with
        | inl y => exact he.elim
        | inr y => exact ⟨x, y, rfl⟩
      | inr y =>
        cases b with
        | inl x => exact ⟨x, y, Sym2.eq_swap⟩
        | inr x => exact he.elim
  choose left right hends using hend
  let g : M → incoming := fun e => ⟨right e, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, left e, by
      change s(Sum.inl (left e), Sum.inr (right e)) ∈ M
      rw [← hends e]
      exact e.property⟩⟩
  have hg : Function.Injective g := by
    intro e d hed
    apply Subtype.ext
    have hy : right e = right d := congrArg Subtype.val hed
    apply hM.2 e.val e.property d.val d.property (Sum.inr (right e))
    · rw [hends e]
      exact Sym2.mem_mk_right _ _
    · rw [hends d, hy]
      exact Sym2.mem_mk_right _ _
  have hmatching : Nat.card M ≤ incoming.card := by
    simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective g hg
  let fold : P ⊕ P → P := Sum.elim id id
  let excluded := C.toFinset.image fold
  let a := (Finset.univ : Finset P) \ excluded
  have ha : IsAntichain (· ≤ ·) (a : Set P) := by
    intro x hx y hy hne hxy
    have hxy' : x < y := lt_of_le_of_ne hxy hne
    have hc := (Matching.vertexCover_mathlib G C).mp hC
      (show G.Adj (Sum.inl x) (Sum.inr y) from hxy')
    rcases hc with hxC | hyC
    · exact (Finset.mem_sdiff.mp hx).2
        (Finset.mem_image.mpr ⟨Sum.inl x, Set.mem_toFinset.mpr hxC, rfl⟩)
    · exact (Finset.mem_sdiff.mp hy).2
        (Finset.mem_image.mpr ⟨Sum.inr y, Set.mem_toFinset.mpr hyC, rfl⟩)
  have hexcluded : excluded.card ≤ Nat.card C := by
    simpa [excluded, Nat.card_eq_fintype_card] using
      (Finset.card_image_le : (C.toFinset.image fold).card ≤ C.toFinset.card)
  have ha_count : a.card + excluded.card = Fintype.card P := by
    simpa [a] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ excluded)
  refine ⟨p, a, hp, ha, Nat.le_antisymm ?_ (antichain_le_partition p hp a ha)⟩
  omega

/-- Every antichain is bounded by the width, defined independently as the
maximum over all antichains. -/
lemma antichain_le_width (a : Finset P)
    (ha : IsAntichain (· ≤ ·) (a : Set P)) : a.card ≤ width P := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)

/-- Dilworth's equality, with an attained partition and antichain and the two
universal extremal bounds. -/
theorem dilworth : Specs.FiniteCombinatorics.Graph.Orders.Dilworth.dilworthType := by
  intro P _ _
  classical
  obtain ⟨p, a, hp, ha, heq⟩ := exists_equal_chain_partition_antichain (P := P)
  have hmax : ∀ b : Finset P, IsAntichain (· ≤ ·) (b : Set P) → b.card ≤ a.card := by
    intro b hb
    rw [← heq]
    exact antichain_le_partition p hp b hb
  have hwidth : a.card = width P := by
    apply Nat.le_antisymm (antichain_le_width a ha)
    exact Finset.sup_le (fun b hb => hmax b (Finset.mem_filter.mp hb).2)
  exact ⟨p, a, hp, ha, heq, hwidth, hmax, fun q hq =>
    heq.trans_le (antichain_le_partition q hq a ha)⟩

/-- For the empty poset the width is zero and its chain partition has no parts. -/
theorem dilworth_empty : Specs.FiniteCombinatorics.Graph.Orders.Dilworth.emptyType := by
  intro P _ _ _
  classical
  obtain ⟨p, a, hp, _, heq, hwidth, _, _⟩ := dilworth P
  have ha : a = ∅ := Finset.eq_empty_of_isEmpty a
  have hz : Specs.FiniteCombinatorics.Graph.Orders.Dilworth.widthValue P = 0 :=
    hwidth.symm.trans (by simp [ha])
  exact ⟨hz, p, hp, Finset.card_eq_zero.mp (by rw [heq, ha]; rfl)⟩

end FiniteCombinatorics.Graph.Orders
