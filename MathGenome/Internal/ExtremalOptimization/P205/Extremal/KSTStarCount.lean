import MathGenome.Internal.ExtremalOptimization.Specs.P205.Extremal.KSTStarCount
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace P205.Extremal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem mem_commonNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    v ∈ commonNeighborFinset G S ↔ ∀ u ∈ S, G.Adj v u := by
  simp [commonNeighborFinset]

theorem commonNeighbors_disjoint : KSTStarCountSpec.commonNeighborsDisjoint := by
  intro V _ _ G _ S
  apply Finset.disjoint_left.mpr
  intro v hv hcommon
  exact G.loopless.irrefl v ((mem_commonNeighborFinset G S v).mp hcommon v hv)

theorem commonNeighbors_card_le : KSTStarCountSpec.commonNeighborsBound := by
  intro V _ _ G _ s t hs hst hfree S hS
  have hlt : (commonNeighborFinset G S).card < t := by
    by_contra h
    obtain ⟨B, hB, hcard⟩ :=
      Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
    apply hfree
    refine ⟨S, B, hS, hcard, ?_, ?_⟩
    · exact Finset.disjoint_of_subset_right hB (commonNeighbors_disjoint G S)
    · intro a ha b hb
      exact G.adj_symm ((mem_commonNeighborFinset G S b).mp (hB hb) a ha)
  omega

/-- Exact double count of stars; no forbidden-subgraph hypothesis is needed. -/
theorem star_count_eq (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    (∑ v : V, Nat.choose (G.degree v) s) =
      ∑ S ∈ (univ : Finset V).powersetCard s, (commonNeighborFinset G S).card := by
  classical
  let r : V → Finset V → Prop := fun v S => ∀ u ∈ S, G.Adj v u
  have habove (v : V) :
      ((univ : Finset V).powersetCard s).bipartiteAbove r v =
        (G.neighborFinset v).powersetCard s := by
    ext S
    simp only [Finset.mem_bipartiteAbove, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    constructor
    · rintro ⟨hcard, hadj⟩
      exact ⟨fun u hu => (G.mem_neighborFinset v u).mpr (hadj u hu), hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨hcard, fun u hu => (G.mem_neighborFinset v u).mp (hsub hu)⟩
  have hbelow (S : Finset V) :
      (univ : Finset V).bipartiteBelow r S = commonNeighborFinset G S := rfl
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset V)) (t := (univ : Finset V).powersetCard s) r
  simpa only [habove, hbelow, Finset.card_powersetCard,
    G.card_neighborFinset_eq_degree] using hcount

theorem star_count_le : KSTStarCountSpec.starCountBound := by
  intro V _ _ G _ s t hs hst hfree
  rw [star_count_eq]
  calc
    _ ≤ ∑ S ∈ (univ : Finset V).powersetCard s, (t - 1) := by
      apply Finset.sum_le_sum
      intro S hS
      exact commonNeighbors_card_le G s t hs hst hfree S (Finset.mem_powersetCard.mp hS).2
    _ = (t - 1) * Nat.choose (Fintype.card V) s := by
      simp [Finset.card_powersetCard, Nat.mul_comm]

end P205.Extremal
