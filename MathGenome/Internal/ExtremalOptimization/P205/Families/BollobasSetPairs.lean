import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.BollobasSetPairs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Convert

open scoped BigOperators
open Finset

namespace P205

private noncomputable def weight (a b : ℕ) : ℝ := (Nat.choose (a + b) a : ℝ)⁻¹

private lemma weight_step {a b : ℕ} (ha : 0 < a) :
    (a : ℝ) * weight (a - 1) b = (a + b : ℕ) * weight a b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have h := Nat.add_one_mul_choose_eq (a + b) a
  have h' : ((a + 1 + b : ℕ) : ℝ) * (Nat.choose (a + b) a : ℝ) =
      (Nat.choose (a + 1 + b) (a + 1) : ℝ) * (a + 1 : ℕ) := by
    exact_mod_cast (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
  have h₁ : (Nat.choose (a + b) a : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  have h₂ : (Nat.choose (a + 1 + b) (a + 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  simp only [weight, Nat.succ_sub_one, Nat.succ_eq_add_one]
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h₁ h₂]
  simpa [mul_comm] using h'.symm

private lemma weight_erase_sum {α : Type*} [DecidableEq α]
    (U A B : Finset α) (hA : A ⊆ U) (hB : B ⊆ U)
    (hd : Disjoint A B) (hne : A.Nonempty) :
    ∑ x ∈ U, (if x ∈ B then 0 else weight (A.erase x).card B.card) =
      (U.card : ℝ) * weight A.card B.card := by
  have hAB : A ⊆ U \ B := fun x hx => mem_sdiff.mpr
    ⟨hA hx, fun hb => (disjoint_left.mp hd hx hb)⟩
  calc
    _ = ∑ x ∈ U \ B, weight (A.erase x).card B.card := by
      symm
      calc
        _ = ∑ x ∈ U, (if x ∉ B then weight (A.erase x).card B.card else 0) := by
          rw [← sum_filter]
          congr 1
          ext x
          simp
        _ = _ := by
          apply sum_congr rfl
          intro x hx
          by_cases h : x ∈ B <;> simp [h]
    _ = (∑ x ∈ A, weight (A.erase x).card B.card) +
        ∑ x ∈ (U \ B) \ A, weight (A.erase x).card B.card := by
      rw [add_comm, sum_sdiff hAB]
    _ = (A.card : ℝ) * weight (A.card - 1) B.card +
        (((U \ B) \ A).card : ℝ) * weight A.card B.card := by
      congr 1
      · rw [show (∑ x ∈ A, weight (A.erase x).card B.card) =
            ∑ _x ∈ A, weight (A.card - 1) B.card from
            sum_congr rfl (fun x hx => by rw [card_erase_of_mem hx])]
        simp
      · rw [show (∑ x ∈ (U \ B) \ A, weight (A.erase x).card B.card) =
            ∑ _x ∈ (U \ B) \ A, weight A.card B.card from
            sum_congr rfl (fun x hx => by rw [erase_eq_of_notMem (mem_sdiff.mp hx).2])]
        simp
    _ = _ := by
      rw [weight_step hne.card_pos]
      have hcard₁ := card_sdiff_add_card_eq_card hB
      have hcard₂ := card_sdiff_add_card_eq_card hAB
      have hr₁ : (((U \ B).card : ℕ) : ℝ) + B.card = U.card := by exact_mod_cast hcard₁
      have hr₂ : ((((U \ B) \ A).card : ℕ) : ℝ) + A.card = (U \ B).card := by exact_mod_cast hcard₂
      push_cast
      linear_combination weight A.card B.card * hr₁ + weight A.card B.card * hr₂

/-- Induction on a finite ground set containing all the pairs. -/
private lemma ground_bound {α ι : Type*} [DecidableEq α] (U : Finset α) :
    ∀ (I : Finset ι) (A B : ι → Finset α),
      (∀ i ∈ I, A i ⊆ U) → (∀ i ∈ I, B i ⊆ U) →
      (∀ i ∈ I, Disjoint (A i) (B i)) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → ((A i) ∩ (B j)).Nonempty) →
      ∑ i ∈ I, weight (A i).card (B i).card ≤ 1 := by
  classical
  refine Finset.strongInductionOn U ?_
  intro U ih I A B hA hB hd hc
  by_cases he : ∃ i ∈ I, A i = ∅
  · obtain ⟨i, hi, hai⟩ := he
    have hI : I = {i} := eq_singleton_iff_unique_mem.mpr ⟨hi, by
      intro j hj
      by_contra hji
      obtain ⟨x, hx⟩ := hc i hi j hj (Ne.symm hji)
      simp [hai] at hx⟩
    simp [hI, hai, weight]
  have hne : ∀ i ∈ I, (A i).Nonempty := by
    intro i hi
    exact nonempty_iff_ne_empty.mpr (fun h => he ⟨i, hi, h⟩)
  by_cases hI : I.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hI
    have hU : (0 : ℝ) < U.card := by
      exact_mod_cast lt_of_lt_of_le (hne i₀ hi₀).card_pos (card_le_card (hA i₀ hi₀))
    have hpoint : ∀ x ∈ U,
        ∑ i ∈ I, (if x ∈ B i then 0 else weight ((A i).erase x).card (B i).card) ≤ 1 := by
      intro x hx
      have hb := ih (U.erase x) (erase_ssubset hx)
        (I.filter (fun i => x ∉ B i)) (fun i => (A i).erase x) B
      have ht : ∑ i ∈ I.filter (fun i => x ∉ B i),
          weight ((A i).erase x).card (B i).card ≤ 1 := by
        apply hb
        · intro i hi
          exact erase_subset_erase x (hA i (mem_filter.mp hi).1)
        · intro i hi
          exact subset_erase.mpr ⟨hB i (mem_filter.mp hi).1, (mem_filter.mp hi).2⟩
        · intro i hi
          exact (hd i (mem_filter.mp hi).1).mono_left (erase_subset x (A i))
        · intro i hi j hj hij
          obtain ⟨y, hy⟩ := hc i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij
          have hyi := (mem_inter.mp hy).1
          have hyj := (mem_inter.mp hy).2
          exact ⟨y, mem_inter.mpr ⟨mem_erase.mpr ⟨by
            intro hxy
            subst y
            exact (mem_filter.mp hj).2 hyj, hyi⟩, hyj⟩⟩
      convert ht using 1
      rw [sum_filter]
      apply sum_congr rfl
      intro i hi
      by_cases h : x ∈ B i <;> simp [h]
    have hsum := sum_le_sum hpoint
    have heq : (∑ x ∈ U, ∑ i ∈ I,
          (if x ∈ B i then 0 else weight ((A i).erase x).card (B i).card)) =
        (U.card : ℝ) * ∑ i ∈ I, weight (A i).card (B i).card := by
      rw [sum_comm, mul_sum]
      apply sum_congr rfl
      intro i hi
      exact weight_erase_sum U (A i) (B i) (hA i hi) (hB i hi) (hd i hi) (hne i hi)
    rw [heq] at hsum
    simp only [sum_const, nsmul_eq_mul, mul_one] at hsum
    exact (mul_le_mul_iff_right₀ hU).mp (by simpa [mul_comm] using hsum)
  · simp [not_nonempty_iff_eq_empty.mp hI]

/-- Bollobás's set-pair inequality, with no finiteness assumption on the ambient type. -/
theorem bollobas_set_pairs : Specs.P205.BollobasSetPairs := by
  intro α ι _ I A B hd hc
  classical
  let U := I.biUnion (fun i => A i ∪ B i)
  apply ground_bound U I A B
  · intro i hi x hx
    exact mem_biUnion.mpr ⟨i, hi, mem_union_left _ hx⟩
  · intro i hi x hx
    exact mem_biUnion.mpr ⟨i, hi, mem_union_right _ hx⟩
  · exact hd
  · exact hc

end P205
