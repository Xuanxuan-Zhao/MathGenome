import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.PartialSummation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

open Finset MeasureTheory
open scoped Interval

namespace P203.PartialSummation

/-- Theorem 3.6 (`nt:C06`), finite ring-valued partial summation. -/
theorem discrete : P203Specs.PartialSummation.discreteType := by
  intro R _ c w m N hm hN
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton, Finset.Ico_self, Finset.sum_empty]
    have h : (∑ n ∈ Finset.Icc 1 m, c n) = (∑ n ∈ Finset.Icc 1 (m-1), c n) + c m := by
      simpa [Nat.sub_add_cancel hm] using
        (Finset.sum_Icc_succ_top (f := c) (a := 1) (b := m-1) (by omega))
    rw [h]
    ring
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih,
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top (by omega)]
    ring

lemma mem_positive_cutoff {n : ℕ} {t : ℝ} :
    n ∈ Finset.Icc 1 ⌊t⌋₊ ↔ 1 ≤ n ∧ (n : ℝ) ≤ t := by
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨hn, ht⟩
    exact ⟨hn, (Nat.le_floor_iff' (by omega)).mp ht⟩
  · rintro ⟨hn, ht⟩
    exact ⟨hn, (Nat.le_floor_iff' (by omega)).mpr ht⟩

lemma mem_intervalIndices {n : ℕ} {a b : ℝ} :
    n ∈ intervalIndices a b ↔ 1 ≤ n ∧ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  classical
  simp only [intervalIndices, Finset.mem_filter, mem_positive_cutoff]
  tauto

@[simp] lemma intervalIndices_self (a : ℝ) : intervalIndices a a = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have h := mem_intervalIndices.mp hn
  exact (not_lt_of_ge h.2.2) h.2.1

lemma partialSum_below_one {R : Type*} [AddCommMonoid R] (c : ℕ → R)
    {t : ℝ} (ht : t < 1) : partialSum c t = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have h := mem_positive_cutoff.mp hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.1
  exact False.elim ((not_le_of_gt ht) (hn1.trans h.2))

@[simp] lemma partialSum_nat {R : Type*} [AddCommMonoid R] (c : ℕ → R) (N : ℕ) :
    partialSum c N = ∑ n ∈ Finset.Icc 1 N, c n := by
  simp only [partialSum, Nat.floor_natCast]

lemma partialSum_eq_sum_cutoff {R : Type*} [AddCommMonoid R] (c : ℕ → R)
    {t b : ℝ} (htb : t ≤ b) :
    partialSum c t = ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, if (n : ℝ) ≤ t then c n else 0 := by
  classical
  change (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n) = _
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, mem_positive_cutoff]
  constructor
  · rintro ⟨hn, ht⟩
    exact ⟨⟨hn, ht.trans htb⟩, ht⟩
  · exact fun h => ⟨h.1.1, h.2⟩

lemma partialSum_decomposition {R : Type*} [AddCommMonoid R] (c : ℕ → R)
    {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    partialSum c t = partialSum c a +
      ∑ n ∈ intervalIndices a b, if (n : ℝ) ≤ t then c n else 0 := by
  classical
  rw [partialSum_eq_sum_cutoff c htb, partialSum_eq_sum_cutoff c (hat.trans htb)]
  simp only [intervalIndices, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hna : (n : ℝ) ≤ a
  · simp [hna, not_lt.mpr hna, hna.trans hat]
  · simp [hna, lt_of_not_ge hna]

lemma partialSum_decomposition_top {R : Type*} [AddCommMonoid R] (c : ℕ → R)
    {a b : ℝ} (hab : a ≤ b) :
    partialSum c b = partialSum c a + ∑ n ∈ intervalIndices a b, c n := by
  classical
  rw [partialSum_decomposition c hab le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := mem_positive_cutoff.mp (Finset.mem_filter.mp hn).1
  simp [hn'.2]

lemma C1Weight.ftc {K : Type*} [RCLike K] {w w' : ℝ → K} {a b u v : ℝ}
    (hw : C1Weight w w' a b) (huv : u ≤ v) (hau : a ≤ u) (hvb : v ≤ b) :
    ∫ t in u..v, w' t = w v - w u := by
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hau hvb
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv (hw.1.mono hsub)
  · intro t ht
    exact (hw.2.2 t (hsub (Set.mem_Icc_of_Ioo ht))).hasDerivAt
      (Icc_mem_nhds (hau.trans_lt ht.1) (ht.2.trans_le hvb))
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr
      ((hw.2.1.mono hsub).integrableOn_Icc)

lemma C1Weight.integrable_step {K : Type*} [RCLike K] {w w' : ℝ → K} {a b : ℝ}
    (hw : C1Weight w w' a b) (hab : a ≤ b) (u : ℝ) :
    IntervalIntegrable (fun t => if u ≤ t then w' t else 0) volume a b := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (hw.2.1.integrableOn_Icc.indicator measurableSet_Ici)

lemma C1Weight.integral_step {K : Type*} [RCLike K] {w w' : ℝ → K} {a b u : ℝ}
    (hw : C1Weight w w' a b) (hau : a < u) (hub : u ≤ b) :
    ∫ t in a..b, (if u ≤ t then w' t else 0) = w b - w u := by
  have hab : a ≤ b := hau.le.trans hub
  have hi : Set.Ici u ∩ Set.Ioc a b = Set.Icc u b := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hau.trans_le h.1, h.2⟩
  change (∫ t in a..b, (Set.Ici u).indicator w' t) = _
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, hi, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hub]
  exact hw.ftc hub hau.le le_rfl

/-- Integrate the finite step decomposition of the partial sums. -/
lemma integral_partialSum {K : Type*} [RCLike K] (c : ℕ → K)
    {w w' : ℝ → K} {a b : ℝ} (hab : a ≤ b) (hw : C1Weight w w' a b) :
    ∫ t in a..b, partialSum c t * w' t =
      partialSum c a * (w b - w a) +
        ∑ n ∈ intervalIndices a b, c n * (w b - w n) := by
  classical
  have hi : IntervalIntegrable w' volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hw.2.1.integrableOn_Icc
  have hs (n : ℕ) : IntervalIntegrable
      (fun t => c n * (if (n : ℝ) ≤ t then w' t else 0)) volume a b :=
    (hw.integrable_step hab n).const_mul (c n)
  have hsum : IntervalIntegrable
      (fun t => ∑ n ∈ intervalIndices a b, c n * (if (n : ℝ) ≤ t then w' t else 0))
      volume a b := by
    simpa only [Finset.sum_fn] using
      (IntervalIntegrable.sum (intervalIndices a b) (fun n _ => hs n))
  calc
    _ = ∫ t in a..b, (partialSum c a * w' t +
          ∑ n ∈ intervalIndices a b, c n * (if (n : ℝ) ≤ t then w' t else 0)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      dsimp only
      rw [partialSum_decomposition c ht.1 ht.2, add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = partialSum c a * (∫ t in a..b, w' t) +
          ∑ n ∈ intervalIndices a b, c n * (∫ t in a..b, if (n : ℝ) ≤ t then w' t else 0) := by
      rw [intervalIntegral.integral_add (hi.const_mul _) hsum,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun n _ => hs n)]
      simp_rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [hw.ftc hab le_rfl le_rfl]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hn, han⟩
      rw [hw.integral_step han (mem_positive_cutoff.mp hn).2]

/-- Theorem 3.6 (`nt:C06`), Abel identity with interval-local C¹ data. -/
theorem abel : P203Specs.PartialSummation.abelType := by
  intro K _ c w w' a b hab hw
  rw [integral_partialSum c hab hw, partialSum_decomposition_top c hab]
  have hs : (∑ n ∈ intervalIndices a b, c n * (w b - w n)) =
      (∑ n ∈ intervalIndices a b, c n) * w b -
        ∑ n ∈ intervalIndices a b, c n * w n := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hs]
  ring

end P203.PartialSummation
