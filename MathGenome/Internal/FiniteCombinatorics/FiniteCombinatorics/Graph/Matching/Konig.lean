import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.AlternatingReach
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Konig
import Mathlib.Data.Finset.Max

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Matching
open Alternating

variable {V : Type u} [Fintype V] {G : SimpleGraph V} {L R : Set V}
  {M : Set (Sym2 V)}

/-- A maximum exists because the family of edge subsets is finite and contains
at least the empty matching. -/
lemma exists_maximum_matching (G : SimpleGraph V) :
    ∃ M : Set (Sym2 V), IsMatching G M ∧
      ∀ N : Set (Sym2 V), IsMatching G N → Nat.card N ≤ Nat.card M := by
  classical
  let s : Finset (Set (Sym2 V)) := Finset.univ.filter (IsMatching G)
  have hs : s.Nonempty := ⟨∅, by simp [s, empty_matching G]⟩
  obtain ⟨M, hM, hmax⟩ := s.exists_max_image (fun N => Nat.card N) hs
  exact ⟨M, (Finset.mem_filter.mp hM).2,
    fun N hN => hmax N (by simp [s, hN])⟩

/-- Alternating search produces a cover with precisely one endpoint of every
matching edge. Counting via injections avoids subtraction of cardinalities. -/
lemma maximum_matching_has_equal_cover (hB : Bipartition G L R)
    (hM : IsMatching G M)
    (hmax : ∀ N : Set (Sym2 V), IsMatching G N → Nat.card N ≤ Nat.card M) :
    ∃ C : Set V, IsVertexCover G C ∧ Nat.card M = Nat.card C := by
  classical
  let S := leftReach G L R M
  let T := rightReach G L R M
  let C := (L \ S) ∪ T
  obtain ⟨hneighbors, hsat, _⟩ := alternating_reachability G L R M hB hM hmax
  have hcover : IsVertexCover G C := by
    apply (vertexCover_mathlib G C).mpr
    intro a b hab
    have hlr : ∀ {x y}, G.Adj x y → x ∈ L → y ∈ R → x ∈ C ∨ y ∈ C := by
      intro x y hxy hx hy
      by_cases hxS : x ∈ S
      · right
        apply Or.inr
        change y ∈ rightReach G L R M
        rw [hneighbors]
        exact ⟨hy, x, hxS, hxy⟩
      · exact Or.inl (Or.inl ⟨hx, hxS⟩)
    rcases hB.crosses hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hlr hab ha hb
    · exact (hlr hab.symm hb ha).symm
  have hCsat : ∀ v ∈ C, Saturated M v := by
    intro v hv
    rcases hv with hv | hv
    · by_contra hfree
      exact hv.2 (root_mem_leftReach ⟨hv.1, hfree⟩)
    · exact hsat v hv
  have hseparate : ∀ a b, s(a, b) ∈ M → a ∈ C → b ∈ C → False := by
    intro a b hab ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rcases hB.crosses (hM.1 hab) with h | h
      · exact hB.not_right hb.1 h.2
      · exact hB.not_right ha.1 h.1
    · have hba : s(b, a) ∈ M := by simpa only [Sym2.eq_swap] using hab
      exact ha.2 (right_partner_reached hB hM hb hba).1
    · exact hb.2 (right_partner_reached hB hM ha hab).1
    · rcases hB.crosses (hM.1 hab) with h | h
      · exact hB.not_left ha.1 h.1
      · exact hB.not_left hb.1 h.2
  have hchoose : ∀ v : C, ∃ e : M, v.val ∈ e.val := by
    intro v
    obtain ⟨e, he, hv⟩ := hCsat v.val v.property
    exact ⟨⟨e, he⟩, hv⟩
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro v w heq
    apply Subtype.ext
    obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp (hf v)
    have hw : w.val ∈ s(v.val, x) := by
      rw [← hx, heq]
      exact hf w
    rcases Sym2.mem_iff.mp hw with h | h
    · exact h.symm
    · have he : s(v.val, x) ∈ M := by rw [← hx]; exact (f v).property
      exact (hseparate v.val x he v.property (h ▸ w.property)).elim
  exact ⟨C, hcover, Nat.le_antisymm (matching_le_cover G M C hM hcover)
    (Nat.card_le_card_of_injective f hinj)⟩

/-- Kőnig's matching--vertex-cover equality, with both extrema attained. -/
theorem konig_matching_cover :
    Specs.FiniteCombinatorics.Graph.Matching.Konig.konig_matching_coverType := by
  intro V _ G L R hB
  obtain ⟨M, hM, hmax⟩ := exists_maximum_matching G
  obtain ⟨C, hC, heq⟩ := maximum_matching_has_equal_cover hB hM hmax
  refine ⟨M, C, hM, hC, heq, hmax, ?_⟩
  intro D hD
  rw [← heq]
  exact matching_le_cover G M D hM hD

end FiniteCombinatorics.Graph.Matching
