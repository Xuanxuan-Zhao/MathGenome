import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Foundation
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Transversal

universe u v
noncomputable section
namespace FiniteCombinatorics.Matroid.Transversal
open Set
set_option maxHeartbeats 800000
variable {α : Type u} {β : Type v}

theorem empty_matchable (R : Set β) (Rel : α → β → Prop) : Matchable R Rel ∅ := by
  refine ⟨fun i => False.elim i.property, ?_, ?_⟩
  · intro i; exact False.elim i.property
  · intro i; exact False.elim i.property

theorem matchable_subset (R : Set β) (Rel : α → β → Prop) (I J : Set α)
    (hJ : Matchable R Rel J) (hIJ : I ⊆ J) : Matchable R Rel I := by
  obtain ⟨f, hf, hr⟩ := hJ
  refine ⟨fun i => f ⟨i, hIJ i.property⟩, ?_, fun i => hr ⟨i, hIJ i.property⟩⟩
  intro i j hij
  exact Subtype.ext (congrArg (fun z : J => z.val) (hf hij))

/-- Extend an injective choice by a right vertex outside its image. -/
private theorem matchable_insert {R : Set β} {Rel : α → β → Prop}
    {I : Set α} {e : α} (f : I → R) (hf : Function.Injective f)
    (hr : ∀ i : I, Rel i.val (f i)) (r : R) (her : Rel e r)
    (hfree : ∀ i, f i ≠ r) : Matchable R Rel (insert e I) := by
  classical
  let g : ↥(insert e I) → R :=
    fun i => if h : i.val = e then r else f ⟨i, (mem_insert_iff.mp i.property).resolve_left h⟩
  refine ⟨g, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val = e <;> by_cases hj : j.val = e
    · exact Subtype.ext (hi.trans hj.symm)
    · have hh : r = f ⟨j, (mem_insert_iff.mp j.property).resolve_left hj⟩ := by
        simpa [g, hi, hj] using hij
      exact (hfree _ hh.symm).elim
    · have hh : f ⟨i, (mem_insert_iff.mp i.property).resolve_left hi⟩ = r := by
        simpa [g, hi, hj] using hij
      exact (hfree _ hh).elim
    · have hh := hf (show f ⟨i, (mem_insert_iff.mp i.property).resolve_left hi⟩ =
          f ⟨j, (mem_insert_iff.mp j.property).resolve_left hj⟩ by simpa [g, hi, hj] using hij)
      exact Subtype.ext (congrArg (fun z : I => z.val) hh)
  · intro i
    dsimp [g]
    split_ifs with hi
    · simpa [hi] using her
    · exact hr ⟨i, (mem_insert_iff.mp i.property).resolve_left hi⟩

/-- A larger injective choice uses some right vertex outside the smaller image. -/
private theorem exists_free_choice {R : Set β} {I J : Set α}
    (hI : I.Finite) (_hJ : J.Finite) (f : I → R) (g : J → R)
    (hg : Function.Injective g) (hlt : I.ncard < J.ncard) :
    ∃ e : J, ∀ i, f i ≠ g e := by
  classical
  by_contra! h
  choose k hk using h
  have hinj : Function.Injective k := by
    intro e d hed
    apply hg
    rw [← hk e, ← hk d, hed]
  have : Finite I := hI.to_subtype
  have : Finite J := _hJ.to_subtype
  have hc := Nat.card_le_card_of_injective k hinj
  change J.ncard ≤ I.ncard at hc
  omega

/-- Induction removes a common left vertex whose J-choice is free for I,
reserving that right vertex until the smaller augmentation has been made. -/
theorem matchable_augmentation (R : Set β) (Rel : α → β → Prop) (I J : Set α)
    (hI : I.Finite) (hJ : J.Finite) (hi : Matchable R Rel I)
    (hj : Matchable R Rel J) (hlt : I.ncard < J.ncard) :
    ∃ e ∈ J \ I, Matchable R Rel (insert e I) := by
  classical
  suffices H : ∀ n (I : Set α), I.ncard = n → I.Finite →
      ∀ (Rel : α → β → Prop) (J : Set α), J.Finite →
      Matchable R Rel I → Matchable R Rel J → I.ncard < J.ncard →
      ∃ e ∈ J \ I, Matchable R Rel (insert e I) from
    H I.ncard I rfl hI Rel J hJ hi hj hlt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I hn hI Rel J hJ hi hj hlt
    obtain ⟨f, hf, hfr⟩ := hi
    obtain ⟨g, hg, hgr⟩ := hj
    obtain ⟨e, hefree⟩ := exists_free_choice hI hJ f g hg hlt
    by_cases heI : e.val ∈ I
    · let I' := I \ {e.val}
      let J' := J \ {e.val}
      let Rel' : α → β → Prop := fun a b => Rel a b ∧ b ≠ (g e).val
      have hi' : Matchable R Rel' I' := by
        refine ⟨fun i => f ⟨i, i.property.1⟩, ?_, ?_⟩
        · intro i j hh
          exact Subtype.ext (congrArg (fun z : I => z.val) (hf hh))
        · intro i
          exact ⟨hfr ⟨i, i.property.1⟩, fun hh => hefree _ (Subtype.ext hh)⟩
      have hj' : Matchable R Rel' J' := by
        refine ⟨fun j => g ⟨j, j.property.1⟩, ?_, ?_⟩
        · intro i j hh
          exact Subtype.ext (congrArg (fun z : J => z.val) (hg hh))
        · intro j
          refine ⟨hgr ⟨j, j.property.1⟩, ?_⟩
          intro hh
          have heq := congrArg Subtype.val (hg (Subtype.ext hh))
          exact j.property.2 heq
      have hcI : I'.ncard + 1 = I.ncard := Set.ncard_sdiff_singleton_add_one heI hI
      have hcJ : J'.ncard + 1 = J.ncard := Set.ncard_sdiff_singleton_add_one e.property hJ
      obtain ⟨x, hx, k, hk, hkr⟩ := ih I'.ncard (by omega) I' rfl
        hI.sdiff Rel' J' hJ.sdiff hi' hj' (by omega)
      have hxI : x ∉ I := by
        intro hxi
        exact hx.2 ⟨hxi, fun hxe => hx.1.2 hxe⟩
      refine ⟨x, ⟨hx.1.1, hxI⟩, ?_⟩
      have hm := matchable_insert k hk (fun i => (hkr i).1) (g e) (hgr e)
        (fun i hh => (hkr i).2 (congrArg Subtype.val hh))
      have heq : insert e.val (insert x I') = insert x I := by
        ext a
        simp only [I', mem_insert_iff, mem_sdiff, mem_singleton_iff]
        by_cases ha : a = e.val <;> simp_all
      rwa [heq] at hm
    · exact ⟨e, ⟨e.property, heI⟩, matchable_insert f hf hfr (g e) (hgr e) hefree⟩

/-- Restrict a saturating matching to its chosen left vertices. -/
private theorem matchable_of_saturation {E : Set α} {R : Set β} [Finite E] [Finite R]
    {Rel : α → β → Prop} {I : Set α} (hIE : I ⊆ E)
    (M : Set (Sym2 (E ⊕ R))) (hM : Graph.Matching.IsMatching (bipartiteGraph E R Rel) M)
    (hsat : ∀ e : E, e.val ∈ I → Graph.Matching.Saturated M (Sum.inl e)) :
    Matchable R Rel I := by
  classical
  have hchoice : ∀ i : I, ∃ r : R,
      s(Sum.inl (⟨i, hIE i.property⟩ : E), Sum.inr r) ∈ M ∧ Rel i.val r.val := by
    intro i
    let e : E := ⟨i, hIE i.property⟩
    have hs : Graph.Matching.Saturated M (Sum.inl e) := hsat e i.property
    obtain ⟨z, hz⟩ := (Graph.Matching.saturated_iff_neighbor M (Sum.inl e)).mp hs
    have ha := hM.1 hz
    cases z with
    | inl e' => exact False.elim ha
    | inr r => exact ⟨r, hz, ha⟩
  choose f hf using hchoice
  refine ⟨f, ?_, fun i => (hf i).2⟩
  intro i j hij
  have heq := hM.2 _ (hf i).1 _ (hf j).1 (Sum.inr (f i))
    (Sym2.mem_mk_right _ _) (by rw [hij]; exact Sym2.mem_mk_right _ _)
  have hleft : (⟨i, hIE i.property⟩ : E) = ⟨j, hIE j.property⟩ := by
    rcases Sym2.eq_iff.mp heq with h | h
    · exact Sum.inl.inj h.1
    · simp at h
  exact Subtype.ext (congrArg (fun z : E => z.val) hleft)

/-- Matchings and injective choices describe exactly the same left supports. -/
theorem choice_iff_matching (E : Set α) (R : Set β) [Finite E] [Finite R]
    (Rel : α → β → Prop) (I : Set α) :
    ChoiceIndependent E R Rel I ↔ MatchingIndependent E R Rel I := by
  classical
  constructor
  · rintro ⟨hIE, f, hf, hr⟩
    let left : I → E := fun i => ⟨i, hIE i.property⟩
    let edge : I → Sym2 (E ⊕ R) := fun i => s(Sum.inl (left i), Sum.inr (f i))
    let M : Set (Sym2 (E ⊕ R)) := range edge
    have hM : Graph.Matching.IsMatching (bipartiteGraph E R Rel) M := by
      constructor
      · rintro _ ⟨i, rfl⟩
        exact hr i
      · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ z hzi hzj
        cases z with
        | inl e =>
          have hi : e = left i := by simpa [edge] using hzi
          have hj : e = left j := by simpa [edge] using hzj
          have hij : i = j := Subtype.ext (congrArg (fun z : E => z.val) (hi.symm.trans hj))
          rw [hij]
        | inr r =>
          have hi : r = f i := by simpa [edge] using hzi
          have hj : r = f j := by simpa [edge] using hzj
          rw [hf (hi.symm.trans hj)]
    refine ⟨hIE, M, hM, ?_⟩
    intro e
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, hei⟩
      have he : e = left i := by simpa [edge] using hei
      have hval : e.val = i.val := congrArg (fun z : E => z.val) he
      exact hval ▸ i.property
    · intro he
      let i : I := ⟨e, he⟩
      exact ⟨edge i, ⟨i, rfl⟩, by simp [edge, left, i]⟩
  · rintro ⟨hIE, M, hM, hsat⟩
    exact ⟨hIE, matchable_of_saturation hIE M hM (fun e he => (hsat e).mpr he)⟩

theorem choice_iff_saturation (E : Set α) (R : Set β) [Finite E] [Finite R]
    (Rel : α → β → Prop) (I : Set α) :
    ChoiceIndependent E R Rel I ↔ Saturable E R Rel I := by
  constructor
  · intro h
    obtain ⟨hIE, M, hM, hs⟩ := (choice_iff_matching E R Rel I).mp h
    exact ⟨hIE, M, hM, fun e he => (hs e).mpr he⟩
  · rintro ⟨hIE, M, hM, hs⟩
    exact ⟨hIE, matchable_of_saturation hIE M hM hs⟩

/-- W76, with a unique matroid on the original ambient type and exact ground. -/
theorem transversal_matroid (E : Set α) (R : Set β) (Rel : α → β → Prop)
    (hE : E.Finite) (_hR : R.Finite) :
    ∃! M : _root_.Matroid α, M.E = E ∧
      ∀ I, M.Indep I ↔ ChoiceIndependent E R Rel I := by
  let S : IndependenceSystem E := {
    finite_ground := hE
    Indep := ChoiceIndependent E R Rel
    empty_indep := ⟨empty_subset _, empty_matchable R Rel⟩
    hereditary := fun {_ _} hJ hIJ => ⟨hIJ.trans hJ.1, matchable_subset R Rel _ _ hJ.2 hIJ⟩
    subset_ground := fun {_} hI => hI.1 }
  have haug : Augmentation S := by
    intro I J hI hJ hlt
    obtain ⟨e, he, hi⟩ := matchable_augmentation R Rel I J (hE.subset hI.1)
      (hE.subset hJ.1) hI.2 hJ.2 hlt
    exact ⟨e, he, Set.insert_subset (hJ.1 he.1) hI.1, hi⟩
  refine ⟨ofAugmentation S haug, ⟨rfl, fun I => Iff.rfl⟩, ?_⟩
  intro M hM
  apply _root_.Matroid.ext_indep hM.1
  intro I _
  exact hM.2 I

/-- The source's formulation, using matchings saturating the given subset. -/
theorem transversal_matroid_matching (E : Set α) (R : Set β) [Finite E] [Finite R]
    (Rel : α → β → Prop) :
    ∃! M : _root_.Matroid α, M.E = E ∧
      ∀ I, M.Indep I ↔ Saturable E R Rel I := by
  obtain ⟨M, hM, huniq⟩ := transversal_matroid E R Rel E.toFinite R.toFinite
  refine ⟨M, ⟨hM.1, fun I => (hM.2 I).trans (choice_iff_saturation E R Rel I)⟩, ?_⟩
  intro N hN
  apply huniq N
  exact ⟨hN.1, fun I => (hN.2 I).trans (choice_iff_saturation E R Rel I).symm⟩

theorem empty_left (R : Set β) (Rel : α → β → Prop) (I : Set α) :
    ChoiceIndependent ∅ R Rel I ↔ I = ∅ := by
  constructor
  · intro h
    exact Set.subset_empty_iff.mp h.1
  · rintro rfl
    exact ⟨Subset.rfl, empty_matchable R Rel⟩

theorem empty_right (Rel : α → β → Prop) (I : Set α) :
    Matchable ∅ Rel I ↔ I = ∅ := by
  constructor
  · rintro ⟨f, _, _⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact (f ⟨i, hi⟩).property
  · rintro rfl
    exact empty_matchable _ _

theorem isolated_not_independent (E : Set α) (R : Set β) (Rel : α → β → Prop)
    (e : α) (he : ∀ r ∈ R, ¬ Rel e r) : ¬ ChoiceIndependent E R Rel {e} := by
  rintro ⟨_, f, _, hf⟩
  exact he (f ⟨e, mem_singleton e⟩) (f _).property (hf ⟨e, mem_singleton e⟩)

end FiniteCombinatorics.Matroid.Transversal
