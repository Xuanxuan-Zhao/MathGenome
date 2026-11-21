import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.FiniteTransportation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Field
import Aesop
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
open Finset

namespace ProbabilityFoundations.Ch06

attribute [local instance] Classical.propDecidable

variable {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- Right neighbors in a finite bipartite graph. -/
def neighbors (E : Finset (L × R)) (I : Finset L) : Finset R :=
  univ.filter (fun j => ∃ i ∈ I, (i, j) ∈ E)

omit [Fintype L] in
@[simp] lemma mem_neighbors {E : Finset (L × R)} {I : Finset L} {j : R} :
    j ∈ neighbors E I ↔ ∃ i ∈ I, (i, j) ∈ E := by simp [neighbors]

@[simp] lemma neighbors_empty (E : Finset (L × R)) : neighbors E ∅ = ∅ := by
  ext j; simp

@[simp] lemma empty_neighbors (I : Finset L) : neighbors (∅ : Finset (L × R)) I = ∅ := by
  ext j; simp

lemma neighbors_mono (E : Finset (L × R)) {I K : Finset L} (h : I ⊆ K) :
    neighbors E I ⊆ neighbors E K := by
  intro j hj
  obtain ⟨i, hi, hij⟩ := mem_neighbors.mp hj
  exact mem_neighbors.mpr ⟨i, h hi, hij⟩

lemma neighbors_union (E : Finset (L × R)) (I K : Finset L) :
    neighbors E (I ∪ K) = neighbors E I ∪ neighbors E K := by
  ext j
  simp only [mem_neighbors, mem_union]
  aesop

lemma neighbors_inter_subset (E : Finset (L × R)) (I K : Finset L) :
    neighbors E (I ∩ K) ⊆ neighbors E I ∩ neighbors E K := by
  intro j hj
  exact mem_inter.mpr ⟨neighbors_mono E inter_subset_left hj,
    neighbors_mono E inter_subset_right hj⟩

lemma neighbors_insert (E : Finset (L × R)) (a : L) (b : R) (I : Finset L) :
    neighbors (insert (a,b) E) I =
      if a ∈ I then insert b (neighbors E I) else neighbors E I := by
  ext j
  simp only [mem_neighbors, mem_insert, Prod.mk.injEq]
  split_ifs <;> simp only [mem_insert, mem_neighbors] <;> aesop

lemma neighbors_insert_eq (E : Finset (L × R)) (a : L) (b : R) (I : Finset L)
    (h : a ∉ I ∨ b ∈ neighbors E I) :
    neighbors (insert (a,b) E) I = neighbors E I := by
  rw [neighbors_insert]
  split_ifs with ha
  · exact insert_eq_of_mem (h.resolve_left (not_not.mpr ha))
  · rfl

omit [Fintype L] in
lemma sum_sub_single (p : L → ℝ) (a : L) (t : ℝ) (I : Finset L) :
    (∑ i ∈ I, (p i - if i = a then t else 0)) =
      (∑ i ∈ I, p i) - if a ∈ I then t else 0 := by
  simp [sum_sub_distrib]

/-- Weighted Hall with capacities: every row demand can be met on allowed edges
if each left cut has enough neighboring column capacity. -/
theorem weighted_hall (E : Finset (L × R)) (p : L → ℝ) (q : R → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hcut : ∀ I : Finset L, (∑ i ∈ I, p i) ≤ ∑ j ∈ neighbors E I, q j) :
    ∃ m : L → R → ℝ, (∀ i j, 0 ≤ m i j) ∧
      (∀ i j, (i,j) ∉ E → m i j = 0) ∧
      (∀ i, ∑ j, m i j = p i) ∧ (∀ j, ∑ i, m i j ≤ q j) := by
  classical
  induction E using Finset.induction_on generalizing p q with
  | empty =>
    have hz (i : L) : p i = 0 := by
      have := hcut {i}
      simpa using le_antisymm (by simpa using this) (hp i)
    exact ⟨fun _ _ => 0, by simp, by simp, by simp [hz], by simpa using hq⟩
  | @insert e E he ih =>
    obtain ⟨a,b⟩ := e
    obtain ⟨K, _, hK⟩ := exists_max_image (univ : Finset (Finset L))
      (fun I => (∑ i ∈ I, p i) - ∑ j ∈ neighbors E I, q j) univ_nonempty
    let t := (∑ i ∈ K, p i) - ∑ j ∈ neighbors E K, q j
    have hmax (I : Finset L) :
        (∑ i ∈ I, p i) - ∑ j ∈ neighbors E I, q j ≤ t := hK I (mem_univ _)
    have ht : 0 ≤ t := by simpa using hmax ∅
    by_cases ht0 : t = 0
    · obtain ⟨m, hm, hs, hr, hc⟩ := ih p q hp hq (fun I => by
        have := hmax I
        rw [ht0] at this
        linarith)
      exact ⟨m, hm, fun i j hij => hs i j (fun h => hij (mem_insert_of_mem h)), hr, hc⟩
    have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have haK : a ∈ K := by
      by_contra ha
      have h := hcut K
      rw [neighbors_insert_eq E a b K (Or.inl ha)] at h
      dsimp [t] at htp
      linarith
    have hbK : b ∉ neighbors E K := by
      intro hb
      have h := hcut K
      rw [neighbors_insert_eq E a b K (Or.inr hb)] at h
      dsimp [t] at htp
      linarith
    have htq : t ≤ q b := by
      have h := hcut K
      rw [neighbors_insert, ite_eq_left haK, sum_insert hbK] at h
      dsimp [t]
      linarith
    have htp' : t ≤ p a := by
      have h := hcut (K.erase a)
      rw [neighbors_insert_eq E a b (K.erase a) (Or.inl (by simp))] at h
      have hsub := sum_le_sum_of_subset_of_nonneg
        (neighbors_mono E (erase_subset a K)) (fun j _ _ => hq j)
      have hsum := sum_erase_add K p haK
      dsimp [t]
      linarith
    let p' : L → ℝ := fun i => p i - if i = a then t else 0
    let q' : R → ℝ := fun j => q j - if j = b then t else 0
    have hp' (i : L) : 0 ≤ p' i := by
      dsimp [p']; split_ifs with h
      · subst i; linarith
      · simpa using hp i
    have hq' (j : R) : 0 ≤ q' j := by
      dsimp [q']; split_ifs with h
      · subst j; linarith
      · simpa using hq j
    have hcut' (I : Finset L) : (∑ i ∈ I, p' i) ≤ ∑ j ∈ neighbors E I, q' j := by
      dsimp only [p', q']
      rw [sum_sub_single, sum_sub_single]
      by_cases haI : a ∈ I <;> by_cases hbI : b ∈ neighbors E I
      · simp only [ite_eq_left haI, ite_eq_left hbI]
        have h := hcut I
        rw [neighbors_insert_eq E a b I (Or.inr hbI)] at h
        linarith
      · simp only [ite_eq_left haI, ite_eq_right hbI, sub_zero]
        have := hmax I
        linarith
      · simp only [ite_eq_right haI, ite_eq_left hbI, sub_zero]
        have hu := hcut (I ∪ K)
        rw [neighbors_insert_eq E a b (I ∪ K)
          (Or.inr (neighbors_mono E subset_union_left hbI)), neighbors_union] at hu
        have hi := hcut (I ∩ K)
        rw [neighbors_insert_eq E a b (I ∩ K)
          (Or.inl (fun h => haI (mem_inter.mp h).1))] at hi
        have hsub := sum_le_sum_of_subset_of_nonneg (neighbors_inter_subset E I K)
          (fun j _ _ => hq j)
        have hleft : (∑ i ∈ I ∪ K, p i) + (∑ i ∈ I ∩ K, p i) =
            (∑ i ∈ I, p i) + (∑ i ∈ K, p i) := sum_union_inter
        have hright : (∑ j ∈ neighbors E I ∪ neighbors E K, q j) +
            (∑ j ∈ neighbors E I ∩ neighbors E K, q j) =
            (∑ j ∈ neighbors E I, q j) + (∑ j ∈ neighbors E K, q j) := sum_union_inter
        dsimp [t]
        linarith
      · simp only [ite_eq_right haI, ite_eq_right hbI, sub_zero]
        have h := hcut I
        rwa [neighbors_insert_eq E a b I (Or.inl haI)] at h
    obtain ⟨m, hm, hs, hr, hc⟩ := ih p' q' hp' hq' hcut'
    refine ⟨fun i j => m i j + if i = a ∧ j = b then t else 0, ?_, ?_, ?_, ?_⟩
    · intro i j
      exact add_nonneg (hm i j) (by split_ifs <;> positivity)
    · intro i j hij
      have hne : ¬(i = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩; exact hij (mem_insert_self _ _)
      dsimp only
      rw [hs i j (fun h => hij (mem_insert_of_mem h)), ite_eq_right hne, add_zero]
    · intro i
      rw [sum_add_distrib, hr]
      simp only [ite_and]
      by_cases hi : i = a <;> simp [hi, p']
    · intro j
      rw [sum_add_distrib]
      have h := hc j
      simp only [ite_and]
      by_cases hj : j = b <;> simp [hj, q'] at h ⊢ <;> linarith

omit [DecidableEq L] [DecidableEq R] in
/-- Nonnegative finite vectors of the same mass have a joint matrix, even
when their common mass is zero. -/
theorem matrix_of_equal_nonnegative_sums (r : L → ℝ) (c : R → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j) (hsum : (∑ i, r i) = ∑ j, c j) :
    ∃ k : L → R → ℝ, (∀ i j, 0 ≤ k i j) ∧
      (∀ i, ∑ j, k i j = r i) ∧ (∀ j, ∑ i, k i j = c j) := by
  by_cases hz : (∑ i, r i) = 0
  · have hr0 (i : L) : r i = 0 := by
      have h := single_le_sum (fun i _ => hr i) (mem_univ i)
      exact le_antisymm (by linarith) (hr i)
    have hc0 (j : R) : c j = 0 := by
      have h := single_le_sum (fun j _ => hc j) (mem_univ j)
      exact le_antisymm (by linarith) (hc j)
    exact ⟨fun _ _ => 0, by simp, by simp [hr0], by simp [hc0]⟩
  · refine ⟨fun i j => r i * c j / (∑ i, r i), ?_, ?_, ?_⟩
    · intro i j
      exact div_nonneg (mul_nonneg (hr i) (hc j)) (sum_nonneg (fun i _ => hr i))
    · intro i
      rw [← sum_div, ← mul_sum, ← hsum, mul_div_cancel_right₀ _ hz]
    · intro j
      rw [← sum_div, ← sum_mul, mul_div_cancel_left₀ _ hz]

/-- A supported partial transport which misses at most the defect in total. -/
theorem partial_transportation (p : L → ℝ) (q : R → ℝ) (A : L → R → Prop) (δ : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hcut : ∀ I : Finset L, (∑ i ∈ I, p i) ≤
      (∑ j ∈ univ.filter (fun j => ∃ i ∈ I, A i j), q j) + δ) :
    ∃ f : L → R → ℝ, (∀ i j, 0 ≤ f i j) ∧
      (∀ i j, ¬ A i j → f i j = 0) ∧
      (∀ i, ∑ j, f i j ≤ p i) ∧ (∀ j, ∑ i, f i j ≤ q j) ∧
      (∑ i, (p i - ∑ j, f i j)) ≤ δ := by
  classical
  have hδ : 0 ≤ δ := by simpa using hcut ∅
  let q' : Option R → ℝ := fun j => match j with
    | none => δ
    | some j => q j
  let E : Finset (L × Option R) := univ.filter (fun e => match e.2 with
    | none => True
    | some j => A e.1 j)
  have hq' (j : Option R) : 0 ≤ q' j := by cases j <;> simp [q', hδ, hq]
  have hn (I : Finset L) (j : R) :
      some j ∈ neighbors E I ↔ ∃ i ∈ I, A i j := by simp [E]
  have hnone (I : Finset L) : none ∈ neighbors E I ↔ I.Nonempty := by simp [E, Finset.Nonempty]
  have hcut' (I : Finset L) : (∑ i ∈ I, p i) ≤ ∑ j ∈ neighbors E I, q' j := by
    by_cases hI : I.Nonempty
    · have h := hcut I
      simpa only [sum_filter, neighbors, Fintype.sum_option, q', mem_univ, true_and,
        show (∃ i ∈ I, (i, none) ∈ E) from (mem_neighbors.mp ((hnone I).mpr hI)),
        ↓reduceIte, show ∀ j, (∃ i ∈ I, (i, some j) ∈ E) ↔ ∃ i ∈ I, A i j from
          fun j => by simpa only [mem_neighbors] using hn I j, add_comm] using h
    · have hI0 : I = ∅ := not_nonempty_iff_eq_empty.mp hI
      simp [hI0]
  obtain ⟨g, hg, hgs, hgr, hgc⟩ := weighted_hall E p q' hp hq' hcut'
  have hrow (i : L) : g i none + (∑ j, g i (some j)) = p i := by
    simpa only [Fintype.sum_option] using hgr i
  refine ⟨fun i j => g i (some j), fun i j => hg i (some j), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hgs i (some j) (by simpa [E] using hij)
  · intro i
    have := hg i none
    linarith [hrow i]
  · intro j
    exact hgc (some j)
  · have heq (i : L) : p i - ∑ j, g i (some j) = g i none := by linarith [hrow i]
    simpa only [heq] using hgc none

/-- Finite transportation with a defect, as stated in the source. -/
theorem finite_transportation : Specs.FiniteTransportation := by
  classical
  intro L R _ _ p q A δ hp hq hpsum hqsum hcut
  obtain ⟨f, hf, hfs, hfr, hfc, hdef⟩ := partial_transportation p q A δ hp hq hcut
  let r : L → ℝ := fun i => p i - ∑ j, f i j
  let c : R → ℝ := fun j => q j - ∑ i, f i j
  have hr (i : L) : 0 ≤ r i := sub_nonneg.mpr (hfr i)
  have hc (j : R) : 0 ≤ c j := sub_nonneg.mpr (hfc j)
  have hsum : (∑ i, r i) = ∑ j, c j := by
    simp only [r, c, sum_sub_distrib, hpsum, hqsum]
    rw [sum_comm]
  obtain ⟨k, hk, hkr, hkc⟩ := matrix_of_equal_nonnegative_sums r c hr hc hsum
  refine ⟨fun i j => f i j + k i j, ?_, ?_, ?_, ?_⟩
  · intro i j; exact add_nonneg (hf i j) (hk i j)
  · intro i
    change ∑ j, (f i j + k i j) = p i
    rw [sum_add_distrib, hkr]
    dsimp [r]
    ring
  · intro j
    change ∑ i, (f i j + k i j) = q j
    rw [sum_add_distrib, hkc]
    dsimp [c]
    ring
  · calc
      (∑ i, ∑ j, if A i j then 0 else f i j + k i j) ≤ ∑ i, ∑ j, k i j := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        split_ifs with h
        · exact hk i j
        · simp [hfs i j h]
      _ = ∑ i, r i := by simp only [hkr]
      _ ≤ δ := hdef

end ProbabilityFoundations.Ch06
