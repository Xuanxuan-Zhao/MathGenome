import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.CaroWei
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The Caro–Wei bound, by minimum-degree deletion. For every finite
vertex subset we construct an independent subset with size at least the
sum of reciprocal closed-neighborhood sizes. Removing a minimum-degree
vertex and its neighbors discards weight at most one; the reciprocals
on the remaining induced graph can only increase. -/

open scoped BigOperators Classical
open Finset

namespace P205.Probability.CaroWei

variable {V : Type*} (G : SimpleGraph V)

/-- A finite vertex subset contains an independent set at least as large
as its reciprocal induced-degree sum. No finiteness of the ambient type
or nonemptiness of the subset is needed. -/
theorem exists_independent_reciprocal_bound (s : Finset V) :
    ∃ t : Finset V, t ⊆ s ∧ G.IsIndepSet (t : Set V) ∧
      (∑ v ∈ s, (1 : ℝ) / (((s.filter (G.Adj v)).card : ℝ) + 1)) ≤ (t.card : ℝ) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨v, hv, hmin⟩ := s.exists_min_image (fun v => (s.filter (G.Adj v)).card) hs
      let c := insert v (s.filter (G.Adj v))
      let r := s \ c
      have hc : c ⊆ s := by
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact hv
        · exact (mem_filter.mp hx).1
      have hvc : v ∈ c := mem_insert_self _ _
      have hr : r ⊆ s := sdiff_subset
      have hvr : v ∉ r := by simp [r, hvc]
      have hrs : r ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hr, by
        intro he
        exact hvr (he ▸ hv)⟩
      obtain ⟨t, htr, ht, hweight⟩ := ih r hrs
      have hvt : v ∉ t := fun h => hvr (htr h)
      have hind : G.IsIndepSet (↑(insert v t) : Set V) := by
        intro a ha b hb hab
        simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact G.irrefl
        · intro hadj
          exact (mem_sdiff.mp (htr hb)).2 (mem_insert_of_mem (mem_filter.mpr ⟨hr (htr hb), hadj⟩))
        · intro hadj
          exact (mem_sdiff.mp (htr ha)).2 (mem_insert_of_mem (mem_filter.mpr ⟨hr (htr ha), hadj.symm⟩))
        · exact ht ha hb hab
      have hcard : c.card = (s.filter (G.Adj v)).card + 1 := by
        apply card_insert_of_notMem
        simp
      have hsmall : (∑ x ∈ c, (1 : ℝ) / (((s.filter (G.Adj x)).card : ℝ) + 1)) ≤ 1 := by
        calc
          _ ≤ ∑ _x ∈ c, (1 : ℝ) / (((s.filter (G.Adj v)).card : ℝ) + 1) := by
            apply sum_le_sum
            intro x hx
            apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast Nat.add_le_add_right (hmin x (hc hx)) 1
          _ = 1 := by
            rw [sum_const, nsmul_eq_mul, hcard, Nat.cast_add, Nat.cast_one]
            exact mul_one_div_cancel (by positivity)
      have hrest : (∑ x ∈ r, (1 : ℝ) / (((s.filter (G.Adj x)).card : ℝ) + 1)) ≤
          ∑ x ∈ r, (1 : ℝ) / (((r.filter (G.Adj x)).card : ℝ) + 1) := by
        apply sum_le_sum
        intro x hx
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right (card_le_card (filter_subset_filter _ hr)) 1
      refine ⟨insert v t, insert_subset hv (htr.trans hr), hind, ?_⟩
      have hsplit := sum_sdiff hc (f := fun x => (1 : ℝ) / (((s.filter (G.Adj x)).card : ℝ) + 1))
      rw [card_insert_of_notMem hvt, Nat.cast_add, Nat.cast_one]
      dsimp only [r] at hrest hweight
      linarith
    · refine ⟨∅, empty_subset _, ?_, ?_⟩
      · simp [SimpleGraph.IsIndepSet]
      · simp [not_nonempty_iff_eq_empty.mp hs]

/-- Caro–Wei: the sum of reciprocal closed degrees is bounded by the
canonical independence number, including when the vertex type is empty. -/
theorem bound {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1)) ≤ (G.indepNum : ℝ) := by
  classical
  obtain ⟨t, _, ht, h⟩ := exists_independent_reciprocal_bound G univ
  have hd (v : V) : (univ.filter (G.Adj v)).card = G.degree v := by
    rw [← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
  simp only [hd] at h
  exact h.trans (by exact_mod_cast ht.card_le_indepNum)

end P205.Probability.CaroWei
