import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.HungarianStep
import MathGenome.Internal.ExtremalOptimization.P205.Matching.Models
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.AlternatingReach
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false

universe u v
noncomputable section
namespace P205.Matching.Hungarian
open Specs.P205.Matching.Hungarian

abbrev Legal := @Specs.P205.Matching.Hungarian.Legal
abbrev SearchArc := @Specs.P205.Matching.Hungarian.SearchArc
abbrev Reached := @Specs.P205.Matching.Hungarian.Reached
abbrev leftReach := @Specs.P205.Matching.Hungarian.leftReach
abbrev rightReach := @Specs.P205.Matching.Hungarian.rightReach
abbrev Stalled := @Specs.P205.Matching.Hungarian.Stalled
abbrev boundary := @Specs.P205.Matching.Hungarian.boundary
abbrev updateLeft := @Specs.P205.Matching.Hungarian.updateLeft
abbrev updateRight := @Specs.P205.Matching.Hungarian.updateRight
abbrev rowWeights := @Specs.P205.Matching.Hungarian.rowWeights
abbrev initialLeft := @Specs.P205.Matching.Hungarian.initialLeft
abbrev minimumSlack := @Specs.P205.Matching.Hungarian.minimumSlack
abbrev Augments := @Specs.P205.Matching.Hungarian.Augments

variable {L : Type u} {R : Type v} [Fintype L] [Fintype R]
  {G : BipartiteGraph L R} {w : Edge G → ℝ} {u : L → ℝ} {v : R → ℝ}
  {M : Set (Edge G)} {root : L}

private theorem row_nonempty (hP : ∃ P : Set (Edge G), IsPerfectMatching P) (i : L) :
    (rowWeights w i).Nonempty := by
  classical
  obtain ⟨P, hP⟩ := hP
  obtain ⟨e, _, he⟩ := hP.2 (.inl i)
  exact ⟨w e, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, he.symm⟩, rfl⟩⟩

theorem initialization : Specs.P205.Matching.Hungarian.initializationType := by
  intro L R _ _ G w hP
  classical
  have hm (i : L) : initialLeft w i ∈ rowWeights w i ∧
      ∀ a ∈ rowWeights w i, a ≤ initialLeft w i := by
    have hi := row_nonempty (w := w) hP i
    simp only [initialLeft, Specs.P205.Matching.Hungarian.initialLeft, dite_eq_left hi]
    exact ⟨Finset.max'_mem _ _, fun a ha => Finset.le_max' _ a ha⟩
  refine ⟨⟨?_, empty_matching, ?_⟩, hm⟩
  · intro e
    simpa using (hm e.val.1).2 (w e) (Finset.mem_image.mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩)
  · intro e he
    exact False.elim he

private theorem root_reached : Reached w u v M root (.inl root) := .refl

private theorem matched_reach (hM : IsMatching M) (hr : ¬ Covered M (.inl root))
    {e : Edge G} (he : e ∈ M) :
    e.val.1 ∈ leftReach w u v M root ↔ e.val.2 ∈ rightReach w u v M root := by
  constructor
  · intro hi
    rcases Relation.ReflTransGen.cases_tail hi with heq | ⟨x, hx, hxi⟩
    · have hei : e.val.1 = root := Sum.inl.inj heq
      exact (hr ⟨e, he, hei.symm⟩).elim
    · cases x with
      | inl k => exact False.elim hxi
      | inr j =>
        obtain ⟨f, hfi, hfj, hf⟩ := hxi
        have hfe := hM.1 f hf e he hfi
        change Reached w u v M root (.inr e.val.2)
        rw [← hfe, hfj]
        exact hx
  · intro hj
    exact hj.tail ⟨e, rfl, rfl, he⟩

private theorem boundary_slack (h : Legal w u v M) (hr : ¬ Covered M (.inl root))
    {e : Edge G} (he : e ∈ boundary w u v M root) : e ∉ M ∧ 0 < slack w u v e := by
  have hnm : e ∉ M := fun hm => he.2 ((matched_reach h.2.1 hr hm).mp he.1)
  have hnt : ¬ Tight w u v e := by
    intro ht
    exact he.2 (he.1.tail ⟨e, rfl, rfl, hnm, ht⟩)
  refine ⟨hnm, ?_⟩
  have hf := h.1 e
  change 0 < u e.val.1 + v e.val.2 - w e
  change ¬ (u e.val.1 + v e.val.2 = w e) at hnt
  exact sub_pos.mpr (lt_of_le_of_ne hf (Ne.symm hnt))

private theorem reached_left_cases {i : L} (hi : i ∈ leftReach w u v M root) :
    i = root ∨ ∃ e ∈ M, e.val.1 = i ∧ e.val.2 ∈ rightReach w u v M root := by
  rcases Relation.ReflTransGen.cases_tail hi with heq | ⟨x, hx, hxi⟩
  · exact Or.inl (Sum.inl.inj heq)
  · cases x with
    | inl k => exact False.elim hxi
    | inr j =>
      obtain ⟨e, hei, hej, he⟩ := hxi
      exact Or.inr ⟨e, he, hei, by
        change Reached w u v M root (.inr e.val.2)
        rw [hej]
        exact hx⟩

/-- Matching partners biject the reached right side and the reached left side
with the one unmatched root removed. -/
private theorem partner_bijection (hM : IsMatching M) (hr : ¬ Covered M (.inl root))
    (hs : Stalled w u v M root) :
    Nonempty ((rightReach w u v M root) ≃ ↥(leftReach w u v M root \ {root})) := by
  classical
  have hp (j : rightReach w u v M root) :
      ∃ e : Edge G, e ∈ M ∧ e.val.2 = j.val := by
    obtain ⟨e, he, hej⟩ := hs j.val j.property
    exact ⟨e, he, hej.symm⟩
  choose edge hedge hright using hp
  let f : rightReach w u v M root → ↥(leftReach w u v M root \ {root}) := fun j =>
    ⟨(edge j).val.1, (matched_reach hM hr (hedge j)).mpr (by
      change Reached w u v M root (.inr (edge j).val.2)
      rw [hright]
      exact j.property), by
      intro hh
      exact hr ⟨edge j, hedge j, (Set.mem_singleton_iff.mp hh).symm⟩⟩
  have hfval (j) : (f j).val = (edge j).val.1 := rfl
  have hinj : Function.Injective f := by
    intro j k hfk
    have heq := hM.1 _ (hedge j) _ (hedge k) (congrArg Subtype.val hfk)
    apply Subtype.ext
    rw [← hright j, ← hright k, heq]
  have hsurj : Function.Surjective f := by
    intro i
    rcases reached_left_cases i.property.1 with hi | ⟨e, he, hei, hej⟩
    · exact (i.property.2 hi).elim
    · let j : rightReach w u v M root := ⟨e.val.2, hej⟩
      refine ⟨j, Subtype.ext ?_⟩
      have heq := hM.2 _ (hedge j) e he (hright j)
      change (edge j).val.1 = i.val
      rw [heq, hei]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem reached_card : Specs.P205.Matching.Hungarian.reachedCardType := by
  intro L R _ _ G w u v M root h hr hs
  obtain ⟨e⟩ := partner_bijection h.2.1 hr hs
  have hc := Nat.card_congr e
  have hadd := Set.ncard_sdiff_singleton_add_one
    (s := leftReach w u v M root) (a := root)
    (show root ∈ leftReach w u v M root from root_reached)
  change Nat.card ↥(leftReach w u v M root \ {root}) + 1 = _ at hadd
  exact hadd.symm.trans (congrArg (fun n => n + 1) hc.symm)

/-- A perfect matching injects any set of left vertices into its allowed right
neighbors. In particular a surplus of reached left vertices forces a boundary edge. -/
private theorem boundary_nonempty (hP : ∃ P : Set (Edge G), IsPerfectMatching P)
    (hcard : Nat.card (leftReach w u v M root) =
      Nat.card (rightReach w u v M root) + 1) :
    (boundary w u v M root).Nonempty := by
  classical
  obtain ⟨P, hP⟩ := hP
  by_contra hn
  have hp (i : leftReach w u v M root) : ∃ e : Edge G, e ∈ P ∧ e.val.1 = i.val := by
    obtain ⟨e, he, hei⟩ := hP.2 (.inl i.val)
    exact ⟨e, he, hei.symm⟩
  choose edge hedge hleft using hp
  have hright (i : leftReach w u v M root) : (edge i).val.2 ∈ rightReach w u v M root := by
    by_contra hni
    apply hn
    refine ⟨edge i, ?_, hni⟩
    change Reached w u v M root (.inl (edge i).val.1)
    rw [hleft]
    exact i.property
  let f : leftReach w u v M root → rightReach w u v M root :=
    fun i => ⟨(edge i).val.2, hright i⟩
  have hinj : Function.Injective f := by
    intro i k hik
    have heq := hP.1.2 _ (hedge i) _ (hedge k) (congrArg Subtype.val hik)
    apply Subtype.ext
    rw [← hleft i, ← hleft k, heq]
  have hle := Nat.card_le_card_of_injective f hinj
  omega

theorem boundary_properties : Specs.P205.Matching.Hungarian.boundaryType := by
  intro L R _ _ G w u v M root hP h hr hs
  exact ⟨boundary_nonempty hP (reached_card w u v M root h hr hs),
    fun _ he => boundary_slack h hr he⟩

theorem minimum_slack : Specs.P205.Matching.Hungarian.minimumSlackType := by
  intro L R _ _ G w u v M root hP h hr hs
  classical
  obtain ⟨hne, hpos⟩ := boundary_properties w u v M root hP h hr hs
  let s := (Finset.univ.filter (fun e : Edge G => e ∈ boundary w u v M root)).image
    (slack w u v)
  have hsn : s.Nonempty := by
    obtain ⟨e, he⟩ := hne
    exact ⟨slack w u v e, Finset.mem_image.mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩⟩
  have hd : minimumSlack w u v M root = s.min' hsn := by
    change (if h : s.Nonempty then s.min' h else 0) = s.min' hsn
    exact dite_eq_left hsn
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp (Finset.min'_mem s hsn)
  have heb : e ∈ boundary w u v M root := (Finset.mem_filter.mp he).2
  refine ⟨?_, ?_, e, heb, ?_⟩
  · change 0 < minimumSlack w u v M root
    rw [hd, ← heq]
    exact (hpos e heb).2
  · intro f hf
    change minimumSlack w u v M root ≤ slack w u v f
    rw [hd]
    exact Finset.min'_le s _ (Finset.mem_image.mpr
      ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, rfl⟩)
  · exact hd.trans heq.symm

theorem potential_update : Specs.P205.Matching.Hungarian.updateType := by
  intro L R _ _ G w u v M root hP h hr hs
  classical
  let S := leftReach w u v M root
  let T := rightReach w u v M root
  let δ := minimumSlack w u v M root
  let u' := updateLeft u S δ
  let v' := updateRight v T δ
  change Legal w u' v' M ∧
    (∀ x, Reached w u v M root x → Reached w u' v' M root x) ∧
    (∀ x y, Reached w u v M root x → SearchArc w u v M x y →
      SearchArc w u' v' M x y) ∧
    rightReach w u v M root ⊂ rightReach w u' v' M root
  have hm := minimum_slack w u v M root hP h hr hs
  have hd0 : 0 ≤ δ := hm.1.le
  have hup : Legal w u' v' M := by
    refine ⟨?_, h.2.1, ?_⟩
    · intro e
      have hf := h.1 e
      change w e ≤ updateLeft u S δ e.val.1 + updateRight v T δ e.val.2
      by_cases hi : e.val.1 ∈ S <;> by_cases hj : e.val.2 ∈ T
      · simp only [updateLeft, Specs.P205.Matching.Hungarian.updateLeft,
          updateRight, Specs.P205.Matching.Hungarian.updateRight, ite_eq_left hi, ite_eq_left hj]
        linarith only [hf]
      · have hb := hm.2.1 e ⟨hi, hj⟩
        change δ ≤ u e.val.1 + v e.val.2 - w e at hb
        simp only [updateLeft, Specs.P205.Matching.Hungarian.updateLeft,
          updateRight, Specs.P205.Matching.Hungarian.updateRight, ite_eq_left hi, ite_eq_right hj]
        linarith only [hb]
      · simp only [updateLeft, Specs.P205.Matching.Hungarian.updateLeft,
          updateRight, Specs.P205.Matching.Hungarian.updateRight, ite_eq_right hi, ite_eq_left hj]
        linarith only [hf, hd0]
      · simpa only [updateLeft, Specs.P205.Matching.Hungarian.updateLeft,
          updateRight, Specs.P205.Matching.Hungarian.updateRight, ite_eq_right hi, ite_eq_right hj] using hf
    · intro e he
      have ht := h.2.2 e he
      have heq : e.val.1 ∈ S ↔ e.val.2 ∈ T := matched_reach h.2.1 hr he
      change u e.val.1 + v e.val.2 = w e at ht
      change updateLeft u S δ e.val.1 + updateRight v T δ e.val.2 = w e
      by_cases hi : e.val.1 ∈ S
      · have hj := heq.mp hi
        simp only [updateLeft, Specs.P205.Matching.Hungarian.updateLeft,
          updateRight, Specs.P205.Matching.Hungarian.updateRight, ite_eq_left hi, ite_eq_left hj]
        linarith only [ht]
      · have hj := fun hj => hi (heq.mpr hj)
        simpa only [updateLeft, Specs.P205.Matching.Hungarian.updateLeft,
          updateRight, Specs.P205.Matching.Hungarian.updateRight, ite_eq_right hi, ite_eq_right hj] using ht
  have harc : ∀ x y, Reached w u v M root x → SearchArc w u v M x y →
      SearchArc w u' v' M x y := by
    intro x y hx hxy
    cases x with
    | inl i =>
      cases y with
      | inl k => exact False.elim hxy
      | inr j =>
        obtain ⟨e, hei, hej, he, ht⟩ := hxy
        have hi : e.val.1 ∈ S := by
          change Reached w u v M root (.inl e.val.1)
          rw [hei]
          exact hx
        have hj : e.val.2 ∈ T := by
          change Reached w u v M root (.inr e.val.2)
          rw [hej]
          exact hx.tail ⟨e, hei, hej, he, ht⟩
        refine ⟨e, hei, hej, he, ?_⟩
        change updateLeft u S δ e.val.1 + updateRight v T δ e.val.2 = w e
        change u e.val.1 + v e.val.2 = w e at ht
        simp only [updateLeft, Specs.P205.Matching.Hungarian.updateLeft,
          updateRight, Specs.P205.Matching.Hungarian.updateRight, ite_eq_left hi, ite_eq_left hj]
        linarith only [ht]
    | inr j =>
      cases y with
      | inl i => exact hxy
      | inr k => exact False.elim hxy
  have hreach : ∀ x, Reached w u v M root x → Reached w u' v' M root x := by
    intro x hx
    induction hx with
    | refl => exact .refl
    | @tail y z hy hyz ih => exact ih.tail (harc y z hy hyz)
  refine ⟨hup, hreach, harc, ?_⟩
  obtain ⟨e, heb, hδ⟩ := hm.2.2
  have hnm := (boundary_slack h hr heb).1
  have hi : e.val.1 ∈ S := heb.1
  have hj : e.val.2 ∉ T := heb.2
  have ht : Tight w u' v' e := by
    change updateLeft u S δ e.val.1 + updateRight v T δ e.val.2 = w e
    simp only [updateLeft, Specs.P205.Matching.Hungarian.updateLeft,
      updateRight, Specs.P205.Matching.Hungarian.updateRight, ite_eq_left hi, ite_eq_right hj]
    change δ = u e.val.1 + v e.val.2 - w e at hδ
    linarith only [hδ]
  have hn : e.val.2 ∈ rightReach w u' v' M root :=
    (hreach _ heb.1).tail ⟨e, rfl, rfl, hnm, ht⟩
  refine ⟨fun j hj => hreach _ hj, ?_⟩
  intro hsub
  exact heb.2 (hsub hn)

private theorem search_oriented {a b : L ⊕ R} (ha : SearchArc w u v M a b) :
    FiniteCombinatorics.Graph.Matching.Alternating.Oriented (graph G)
      (Set.range Sum.inl) (Set.range Sum.inr) (edgeSet M) a b := by
  cases a with
  | inl i =>
    cases b with
    | inl k => exact False.elim ha
    | inr j =>
      obtain ⟨e, hei, hej, he, _⟩ := ha
      subst i
      subst j
      refine ⟨e.property, Or.inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ?_⟩⟩
      change edgePair e ∉ edgeSet M
      intro hm
      have hem : e ∈ edgePair ⁻¹' edgeSet M := hm
      rw [preimage_edgeSet] at hem
      exact he hem
  | inr j =>
    cases b with
    | inl i =>
      obtain ⟨e, hei, hej, he⟩ := ha
      subst i
      subst j
      refine ⟨e.property, Or.inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ?_⟩⟩
      rw [Sym2.eq_swap]
      exact ⟨e, he, rfl⟩
    | inr k => exact False.elim ha

private theorem search_edge_tight (h : Legal w u v M) {a b : L ⊕ R}
    (ha : SearchArc w u v M a b) :
    ∃ e : Edge G, edgePair e = s(a,b) ∧ Tight w u v e := by
  cases a with
  | inl i =>
    cases b with
    | inl k => exact False.elim ha
    | inr j =>
      obtain ⟨e, hei, hej, _, ht⟩ := ha
      subst i
      subst j
      exact ⟨e, rfl, ht⟩
  | inr j =>
    cases b with
    | inl i =>
      obtain ⟨e, hei, hej, he⟩ := ha
      subst i
      subst j
      exact ⟨e, Sym2.eq_swap, h.2.2 e he⟩
    | inr k => exact False.elim ha

/-- Remove repeated vertices from a directed search walk. Bypass only removes
darts, so every surviving dart still has the required direction and tightness. -/
private theorem reached_path {a b : L ⊕ R}
    (hab : Relation.ReflTransGen (SearchArc w u v M) a b) :
    ∃ p : (graph G).Walk a b, p.IsPath ∧
      ∀ d ∈ p.darts, SearchArc w u v M d.fst d.snd := by
  classical
  have hw : ∃ p : (graph G).Walk a b,
      ∀ d ∈ p.darts, SearchArc w u v M d.fst d.snd := by
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨.nil, by simp⟩
    | @head x y hxy hyb ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨.cons (search_oriented hxy).1 p, ?_⟩
      intro d hd
      simp only [SimpleGraph.Walk.darts_cons, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hxy
      · exact hp d hd
  obtain ⟨p, hp⟩ := hw
  exact ⟨p.bypass, p.bypass_isPath,
    fun d hd => hp d (p.darts_bypass_subset_darts hd)⟩

private theorem sum_bipartition :
    FiniteCombinatorics.Graph.Matching.Alternating.Bipartition (graph G)
      (Set.range Sum.inl) (Set.range Sum.inr) := by
  constructor
  · exact Set.disjoint_left.mpr (by rintro x ⟨i, rfl⟩ ⟨j, hj⟩; cases hj)
  · ext x
    cases x <;> simp
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl k => exact False.elim hab
      | inr j => exact Or.inl ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    | inr j =>
      cases b with
      | inl i => exact Or.inr ⟨⟨j, rfl⟩, ⟨i, rfl⟩⟩
      | inr k => exact False.elim hab

/-- Coordinate transport preserves the number of chosen edges, because the
unordered-edge map is injective on all actual allowed positions. -/
private theorem edgeSet_card (N : Set (Edge G)) : Nat.card (edgeSet N) = Nat.card N :=
  Set.ncard_image_of_injective N edgePair_injective

theorem augmentation : Specs.P205.Matching.Hungarian.augmentationType := by
  intro L R _ _ G w u v M root j h hr hj hfree
  classical
  obtain ⟨p, hp, hdir⟩ := reached_path hj
  have hroot : ¬ FiniteCombinatorics.Graph.Matching.Saturated (edgeSet M) (.inl root) :=
    fun hs => hr ((covered_iff_saturated M _).mpr hs)
  have hend : ¬ FiniteCombinatorics.Graph.Matching.Saturated (edgeSet M) (.inr j) :=
    fun hs => hfree ((covered_iff_saturated M _).mpr hs)
  have hpos : 0 < p.length := by
    apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
    intro hn
    cases hn.eq
  have halt := (FiniteCombinatorics.Graph.Matching.Alternating.oriented_walk_alternates
    sum_bipartition p (fun d hd => search_oriented (hdir d hd))).1
    (show Sum.inl root ∈ Set.range (Sum.inl : L → L ⊕ R) from ⟨root, rfl⟩)
  have haug : FiniteCombinatorics.Graph.Matching.IsAugmentingPath (graph G) (edgeSet M) p :=
    ⟨(matching_iff_mathGenome M).mp h.2.1, hp, hpos, hroot, hend, halt,
      fun hm => hend ⟨_, hm, Sym2.mem_mk_right _ _⟩⟩
  let U := FiniteCombinatorics.Graph.Matching.flipAlong (edgeSet M) p
  have hU : FiniteCombinatorics.Graph.Matching.IsMatching (graph G) U :=
    FiniteCombinatorics.Graph.Matching.flipAlong_isMatching haug
  let N : Set (Edge G) := edgePair ⁻¹' U
  have hN : edgeSet N = U := edgeSet_preimage U hU.1
  refine ⟨N, ⟨p, haug, hdir, hN⟩, ⟨h.1, ?_, ?_⟩, ?_⟩
  · exact (matching_preimage_mathGenome U hU.1).mpr hU
  · intro e he
    have heU : edgePair e ∈ U := he
    rcases heU with hold | hnew
    · have hem : e ∈ edgePair ⁻¹' edgeSet M := hold.1
      rw [preimage_edgeSet] at hem
      exact h.2.2 e hem
    · obtain ⟨d, hd, hde⟩ := List.mem_map.mp hnew.1
      obtain ⟨f, hf, ht⟩ := search_edge_tight h (hdir d hd)
      have hfe : f = e := edgePair_injective (hf.trans hde)
      exact hfe ▸ ht
  · have hc := FiniteCombinatorics.Graph.Matching.flipAlong_card haug
    change Nat.card U = Nat.card (edgeSet M) + 1 at hc
    rw [← hN, edgeSet_card N, edgeSet_card M] at hc
    exact hc

end P205.Matching.Hungarian
