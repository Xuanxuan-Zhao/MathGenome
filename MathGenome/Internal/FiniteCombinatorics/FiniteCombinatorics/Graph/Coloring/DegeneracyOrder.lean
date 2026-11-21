import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import Mathlib.Data.Finset.Card
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder

universe u
noncomputable section
namespace FiniteCombinatorics.Graph

abbrev IsDegenerate : Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder.IsDegenerateType :=
  Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder.IsDegenerateValue

abbrev LaterBound : Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder.LaterBoundType :=
  Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder.LaterBoundValue

abbrev IsRemovalOrder : Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder.IsRemovalOrderType :=
  Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder.IsRemovalOrderValue

/-- The neighbors of a vertex in an induced graph are the adjacent vertices in
its vertex set. This is also the cardinality bridge used in the removal proof. -/
def inducedNeighborEquiv {V : Type u} (G : SimpleGraph V) (S : Set V) (v : S) :
    (G.induce S).neighborSet v ≃ {w : V // w ∈ S ∧ G.Adj v.val w} where
  toFun w := ⟨w.val.val, w.val.property, w.property⟩
  invFun w := ⟨⟨w.val, w.property.1⟩, w.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem degree_removal_correspondence :
    Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder.degree_removal_correspondenceType := by
  intro V _ G v l
  apply Nat.card_congr
  refine (inducedNeighborEquiv G _ _).trans ?_
  exact Equiv.subtypeEquivRight fun w => by
    constructor
    · rintro ⟨h | h, ha⟩
      · subst w
        exact (G.irrefl ha).elim
      · exact ⟨h, ha⟩
    · rintro ⟨h, ha⟩
      exact ⟨Or.inr h, ha⟩

private theorem exists_removal_list {V : Type u} [Finite V] (G : SimpleGraph V)
    (d : ℕ) (hd : IsDegenerate G d) (S : Finset V) :
    ∃ l : List V, l.Nodup ∧ (∀ w, w ∈ l ↔ w ∈ S) ∧ LaterBound G d l := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨v, hv⟩ := hd (S : Set V) hS
      obtain ⟨l, hn, hm, hb⟩ := ih (S.erase v.val) (Finset.erase_ssubset v.property)
      refine ⟨v.val :: l, List.nodup_cons.mpr ⟨?_, hn⟩, ?_, ?_⟩
      · simp [hm]
      · intro w
        simp only [List.mem_cons, hm, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨_, hw⟩)
          · exact v.property
          · exact hw
        · intro hw
          by_cases he : w = v.val
          · exact Or.inl he
          · exact Or.inr ⟨he, hw⟩
      · refine ⟨?_, hb⟩
        refine (Nat.card_le_card_of_injective
          (f := fun w : {w : V // w ∈ l ∧ G.Adj v.val w} =>
            (⟨⟨w.val, (Finset.mem_erase.mp ((hm w.val).mp w.property.1)).2⟩,
              w.property.2⟩ : (G.induce (S : Set V)).neighborSet v)) ?_).trans hv
        intro a b h
        exact Subtype.ext (congrArg (fun w => w.val.val) h)
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      exact ⟨[], List.nodup_nil, by simp, trivial⟩

private theorem low_degree_of_laterBound {V : Type u} [Finite V]
    (G : SimpleGraph V) (d : ℕ) (l : List V) (hb : LaterBound G d l)
    (S : Set V) (hS : S.Nonempty) (hmem : ∀ w ∈ S, w ∈ l) :
    ∃ v : S, degree (G.induce S) v ≤ d := by
  classical
  induction l with
  | nil =>
    obtain ⟨w, hw⟩ := hS
    simpa using hmem w hw
  | cons v l ih =>
    obtain ⟨hv, hl⟩ := hb
    by_cases hvs : v ∈ S
    · refine ⟨⟨v, hvs⟩, ?_⟩
      refine (Nat.card_le_card_of_injective
        (f := fun w : (G.induce S).neighborSet ⟨v, hvs⟩ =>
          (⟨w.val.val, ?_, w.property⟩ : {w : V // w ∈ l ∧ G.Adj v w})) ?_).trans hv
      · have hw := hmem w.val.val w.val.property
        rcases List.mem_cons.mp hw with he | he
        · have ha : G.Adj v w.val.val := w.property
          rw [he] at ha
          exact (G.irrefl ha).elim
        · exact he
      · intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun w : {w : V // w ∈ l ∧ G.Adj v w} => w.val) h
    · apply ih hl
      intro w hw
      rcases List.mem_cons.mp (hmem w hw) with he | he
      · exact (hvs (he ▸ hw)).elim
      · exact he

theorem degeneracy_iff_removal_order :
    Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder.degeneracy_iff_removal_orderType := by
  intro V _ G d
  classical
  constructor
  · intro hd
    let := Fintype.ofFinite V
    obtain ⟨l, hn, hm, hb⟩ := exists_removal_list G d hd Finset.univ
    exact ⟨l, hn, fun v => (hm v).mpr (Finset.mem_univ v), hb⟩
  · rintro ⟨l, hn, hm, hb⟩ S hS
    exact low_degree_of_laterBound G d l hb S hS (fun w _ => hm w)

theorem empty_removal_order :
    Specs.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder.empty_removal_orderType := by
  intro V _ _ G d
  have ho : IsRemovalOrder G d [] :=
    ⟨List.nodup_nil, fun v => isEmptyElim v, trivial⟩
  refine ⟨ho, (degeneracy_iff_removal_order G d).mpr ⟨[], ho⟩, ?_⟩
  intro l _
  cases l with
  | nil => rfl
  | cons v _ => exact isEmptyElim v

end FiniteCombinatorics.Graph
