import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.DegeneracyOrder
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Greedy
import Mathlib.Data.Finset.Card

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Coloring

/-- Color a list in reverse order. Only neighbors in its tail forbid colors. -/
theorem exists_coloring_of_laterBound {V : Type u} [Finite V]
    (G : SimpleGraph V) (d : ℕ) (l : List V) (hb : LaterBound G d l) :
    ∃ f : V → Fin (d + 1),
      ∀ a ∈ l, ∀ b ∈ l, G.Adj a b → f a ≠ f b := by
  classical
  induction l with
  | nil => exact ⟨fun _ => 0, by simp⟩
  | cons v l ih =>
    obtain ⟨hv, hl⟩ := hb
    obtain ⟨f, hf⟩ := ih hl
    let N := {w : V // w ∈ l ∧ G.Adj v w}
    let _ := Fintype.ofFinite N
    let used : Finset (Fin (d + 1)) := Finset.univ.image (fun w : N => f w.val)
    have hused : used.card ≤ d := by
      calc
        used.card ≤ Fintype.card N := by
          simpa [used] using (Finset.card_image_le (s := Finset.univ) (f := fun w : N => f w.val))
        _ = Nat.card N := Nat.card_eq_fintype_card.symm
        _ ≤ d := hv
    have hlt : used.card < (Finset.univ : Finset (Fin (d + 1))).card := by
      simpa using Nat.lt_succ_of_le hused
    obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hcf : ∀ w ∈ l, G.Adj v w → c ≠ f w := by
      intro w hw ha he
      apply hc
      exact Finset.mem_image.mpr ⟨⟨w, hw, ha⟩, Finset.mem_univ _, he.symm⟩
    refine ⟨fun w => if w = v then c else f w, ?_⟩
    intro a ha b hb hab
    by_cases hav : a = v
    · subst a
      have hbv : b ≠ v := hab.ne.symm
      have hbl : b ∈ l := (List.mem_cons.mp hb).resolve_left hbv
      simpa [hbv] using hcf b hbl hab
    · by_cases hbv : b = v
      · subst b
        have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left hav
        simpa [hav] using (hcf a hal hab.symm).symm
      · have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left hav
        have hbl : b ∈ l := (List.mem_cons.mp hb).resolve_left hbv
        simpa [hav, hbv] using hf a hal b hbl hab

theorem colorable_of_degenerate :
    Specs.FiniteCombinatorics.Graph.Coloring.Greedy.colorable_of_degenerateType := by
  intro V _ G d hd
  obtain ⟨l, _, hm, hb⟩ := (degeneracy_iff_removal_order G d).mp hd
  obtain ⟨f, hf⟩ := exists_coloring_of_laterBound G d l hb
  exact ⟨SimpleGraph.Coloring.mk f (fun {a b} ha => hf a (hm a) b (hm b) ha)⟩

theorem chromaticNumber_le_of_degenerate :
    Specs.FiniteCombinatorics.Graph.Coloring.Greedy.chromaticNumber_le_of_degenerateType := by
  intro V _ G d hd
  exact (chromaticNumber_minimum G).2 (d + 1) (colorable_of_degenerate G d hd)

theorem chromaticNumber_le_of_degree_le :
    Specs.FiniteCombinatorics.Graph.Coloring.Greedy.chromaticNumber_le_of_degree_leType := by
  intro V _ G Δ hΔ
  apply chromaticNumber_le_of_degenerate G Δ
  intro S hS
  obtain ⟨v, hv⟩ := hS
  refine ⟨⟨v, hv⟩, ?_⟩
  refine (Nat.card_le_card_of_injective
    (f := fun w : (G.induce S).neighborSet ⟨v, hv⟩ =>
      (⟨w.val.val, w.property⟩ : G.neighborSet v)) ?_).trans (hΔ v)
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun w : G.neighborSet v => w.val) h

theorem chromaticNumber_le_maxDegree :
    Specs.FiniteCombinatorics.Graph.Coloring.Greedy.chromaticNumber_le_maxDegreeType := by
  intro V _ G _
  apply chromaticNumber_le_of_degree_le G G.maxDegree
  intro v
  exact (degree_mathlib G v).le.trans (G.degree_le_maxDegree v)

theorem empty_maxDegree :
    Specs.FiniteCombinatorics.Graph.Coloring.Greedy.empty_maxDegreeType := by
  intro V _ _ G _
  exact G.maxDegree_of_subsingleton

end FiniteCombinatorics.Graph.Coloring
