import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.PositiveNegative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Necessary
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.FiniteRearrangement
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! A least-unused-index implementation of the crossing construction.
Zero terms are eligible in both directions. This avoids a separate insertion
map and ensures that the eventual bijection covers all original indices. -/
namespace SingleVariableAnalysis
namespace FiniteRearrangement

open scoped BigOperators Topology

variable (a : ℕ → ℝ) (s : ℝ)

noncomputable def eligible (F : Finset ℕ) (i : ℕ) : Prop :=
  if (∑ j ∈ F, a j) ≤ s then 0 ≤ a i else a i ≤ 0

lemma exists_unused (ha : RealSeriesConditionallyConverges a) (F : Finset ℕ) :
    ∃ i, i ∉ F ∧ eligible a s F i := by
  classical
  obtain ⟨hp, hn⟩ := conditional_sign_sets_infinite a ha
  by_cases h : (∑ j ∈ F, a j) ≤ s
  · obtain ⟨i, hi, hF⟩ := hp.exists_notMem_finset F
    exact ⟨i, hF, by simpa [eligible, h] using hi.le⟩
  · obtain ⟨i, hi, hF⟩ := hn.exists_notMem_finset F
    exact ⟨i, hF, by simpa [eligible, h] using hi.le⟩

noncomputable def next (ha : RealSeriesConditionallyConverges a) (F : Finset ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_unused a s ha F)

lemma next_spec (ha : RealSeriesConditionallyConverges a) (F : Finset ℕ) :
    next a s ha F ∉ F ∧ eligible a s F (next a s ha F) :=
  by
    classical
    exact Nat.find_spec (exists_unused a s ha F)

lemma next_le (ha : RealSeriesConditionallyConverges a) (F : Finset ℕ) (i : ℕ)
    (hi : i ∉ F) (he : eligible a s F i) : next a s ha F ≤ i :=
  by
    classical
    exact Nat.find_min' (exists_unused a s ha F) ⟨hi, he⟩

noncomputable def used (ha : RealSeriesConditionallyConverges a) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => insert (next a s ha (used ha n)) (used ha n)

noncomputable def index (ha : RealSeriesConditionallyConverges a) (n : ℕ) : ℕ :=
  next a s ha (used a s ha n)

noncomputable def total (ha : RealSeriesConditionallyConverges a) (n : ℕ) : ℝ :=
  ∑ i ∈ used a s ha n, a i

variable {a s} (ha : RealSeriesConditionallyConverges a)

lemma used_succ (n : ℕ) : used a s ha (n + 1) = insert (index a s ha n) (used a s ha n) := rfl

lemma index_unused (n : ℕ) : index a s ha n ∉ used a s ha n :=
  (next_spec a s ha _).1

lemma used_mono : Monotone (used a s ha) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_insert _ _

lemma index_mem {m n : ℕ} (hmn : m < n) : index a s ha m ∈ used a s ha n := by
  apply used_mono ha (Nat.succ_le_of_lt hmn)
  rw [used_succ]
  exact Finset.mem_insert_self _ _

lemma index_injective : Function.Injective (index a s ha) := by
  intro m n he
  rcases lt_trichotomy m n with h | h | h
  · exact False.elim (index_unused ha n (he ▸ index_mem ha h))
  · exact h
  · exact False.elim (index_unused ha m (he.symm ▸ index_mem ha h))

lemma used_image (n : ℕ) : used a s ha n = (Finset.range n).image (index a s ha) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih => rw [used_succ, Finset.range_add_one, Finset.image_insert, ih]

lemma sum_used (b : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ used a s ha n, b i) = ∑ j ∈ Finset.range n, b (index a s ha j) := by
  classical
  rw [used_image]
  exact Finset.sum_image (fun _ _ _ _ h => index_injective ha h)

lemma total_succ (n : ℕ) :
    total a s ha (n + 1) = total a s ha n + a (index a s ha n) := by
  classical
  dsimp [total]
  rw [used_succ, Finset.sum_insert (index_unused ha n), add_comm]

lemma direction (n : ℕ) :
    if total a s ha n ≤ s then 0 ≤ a (index a s ha n)
    else a (index a s ha n) ≤ 0 :=
  (next_spec a s ha _).2

lemma priority (n i : ℕ) (hi : i ∉ used a s ha n)
    (he : if total a s ha n ≤ s then 0 ≤ a i else a i ≤ 0) :
    index a s ha n ≤ i := next_le a s ha _ i hi he

/-- If an index is eligible on an entire tail, the least-index rule exhausts it. -/
lemma covered_of_eventually_eligible (i : ℕ)
    (he : ∃ N, ∀ n ≥ N,
      if total a s ha n ≤ s then 0 ≤ a i else a i ≤ 0) :
    i ∈ Set.range (index a s ha) := by
  classical
  by_contra hi
  obtain ⟨N, hN⟩ := he
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((index_injective (s := s) ha).nat_tendsto_atTop.eventually (Filter.eventually_ge_atTop (i + 1)))
  let n := max N M
  have hnot : i ∉ used a s ha n := by
    rw [used_image]
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    exact hi ⟨j, hj⟩
  have hp := priority ha n i hnot (hN n (le_max_left _ _))
  have hq := hM n (le_max_right _ _)
  omega

/-- A bounded sum of a nonnegative part along an injective enumeration bounds
its original series, provided every nonzero term is covered. -/
lemma part_converges (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, b i ≠ 0 → i ∈ Set.range (index a s ha))
    (hB : ∃ B : ℝ, ∀ n, (∑ i ∈ used a s ha n, b i) ≤ B) :
    RealSeriesConverges b := by
  obtain ⟨B, hB⟩ := hB
  have hg : Summable (fun n => b (index a s ha n)) :=
    summable_of_sum_range_le (fun n => hb _) (fun n => by
      simpa only [← sum_used ha b n] using hB n)
  have hz : ∀ i, i ∉ Set.range (index a s ha) → b i = 0 := by
    intro i hi
    by_contra hn
    exact hi (hc i hn)
  have hsum := ((index_injective ha).hasSum_iff hz).mp hg.hasSum
  refine ⟨∑' n, b (index a s ha n), (realSequenceConverges_iff _ _).mpr ?_⟩
  exact hsum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)

lemma part_bound (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) (N : ℕ) (c D : ℝ)
    (he : ∀ n ≥ N, b (index a s ha n) = c * a (index a s ha n))
    (hD : ∀ n ≥ N, c * (total a s ha n - total a s ha N) ≤ D) :
    ∃ B : ℝ, ∀ n, (∑ i ∈ used a s ha n, b i) ≤ B := by
  classical
  have hid : ∀ n ≥ N, (∑ i ∈ used a s ha n, b i) =
      (∑ i ∈ used a s ha N, b i) + c * (total a s ha n - total a s ha N) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => ring
    | succ n hn ih =>
      rw [used_succ, Finset.sum_insert (index_unused ha n), ih,
        he n hn, total_succ]
      ring
  refine ⟨(∑ i ∈ used a s ha N, b i) + max D 0, fun n => ?_⟩
  rcases le_total N n with hn | hn
  · rw [hid n hn]
    exact add_le_add le_rfl ((hD n hn).trans (le_max_left _ _))
  · have h := Finset.sum_le_sum_of_subset_of_nonneg (used_mono (s := s) ha hn)
      (fun i _ _ => hb i)
    exact h.trans (le_add_of_nonneg_right (le_max_right D 0))

lemma not_eventually_below : ¬ ∃ N, ∀ n ≥ N, total a s ha n ≤ s := by
  rintro ⟨N, hN⟩
  apply (conditional_parts_not_convergent a ha).1
  apply part_converges (s := s) ha (positivePart a)
    (fun i => (positive_negative_part_identities a i).1)
  · intro i hi
    have hp : 0 ≤ a i := by
      by_contra h
      exact hi (by simp [positivePart, le_of_not_ge h])
    apply covered_of_eventually_eligible (s := s) ha i
    exact ⟨N, fun n hn => by simp [hN n hn, hp]⟩
  · apply part_bound (s := s) ha (positivePart a)
      (fun i => (positive_negative_part_identities a i).1) N 1 (s - total a s ha N)
    · intro n hn
      have h : 0 ≤ a (index a s ha n) := by
        simpa [hN n hn] using direction (s := s) ha n
      simp [positivePart, h]
    · intro n hn
      simpa using sub_le_sub_right (hN n hn) (total a s ha N)

lemma not_eventually_above : ¬ ∃ N, ∀ n ≥ N, s < total a s ha n := by
  rintro ⟨N, hN⟩
  apply (conditional_parts_not_convergent a ha).2
  apply part_converges (s := s) ha (negativePart a)
    (fun i => (positive_negative_part_identities a i).2.1)
  · intro i hi
    have hp : a i ≤ 0 := by
      by_contra h
      exact hi (by simp [negativePart, le_of_lt (neg_neg_of_pos (lt_of_not_ge h))])
    apply covered_of_eventually_eligible (s := s) ha i
    exact ⟨N, fun n hn => by simp [not_le_of_gt (hN n hn), hp]⟩
  · apply part_bound (s := s) ha (negativePart a)
      (fun i => (positive_negative_part_identities a i).2.1) N (-1)
      (total a s ha N - s)
    · intro n hn
      have h : a (index a s ha n) ≤ 0 := by
        simpa [not_le_of_gt (hN n hn)] using direction (s := s) ha n
      simp [negativePart, neg_nonneg.mpr h]
    · intro n hn
      have h := hN n hn
      linarith

lemma exists_below (N : ℕ) : ∃ n ≥ N, total a s ha n ≤ s := by
  classical
  by_contra h
  push Not at h
  exact not_eventually_above (s := s) ha ⟨N, h⟩

lemma exists_above (N : ℕ) : ∃ n ≥ N, s < total a s ha n := by
  classical
  by_contra h
  push Not at h
  exact not_eventually_below (s := s) ha ⟨N, h⟩

/-- Both signs, and the zeros, are exhausted by the greedy enumeration. -/
lemma index_surjective : Function.Surjective (index a s ha) := by
  classical
  intro i
  by_contra hi
  have hnot : i ∉ Set.range (index a s ha) := by simpa [Set.mem_range] using hi
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((index_injective (s := s) ha).nat_tendsto_atTop.eventually
      (Filter.eventually_ge_atTop (i + 1)))
  have hprio : ∀ n ≥ M,
      (if total a s ha n ≤ s then 0 ≤ a i else a i ≤ 0) → False := by
    intro n hn he
    have hu : i ∉ used a s ha n := by
      rw [used_image]
      intro h
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      exact hnot ⟨j, hj⟩
    have hp := priority ha n i hu he
    have hq := hM n hn
    omega
  rcases le_total 0 (a i) with hp | hn
  · obtain ⟨n, hn, hlow⟩ := exists_below (s := s) ha M
    exact hprio n hn (by simp [hlow, hp])
  · obtain ⟨n, hn, hhigh⟩ := exists_above (s := s) ha M
    exact hprio n hn (by simp [not_le_of_gt hhigh, ‹a i ≤ 0›])

/-- Crossings continue arbitrarily far into the enumeration. -/
lemma exists_upcrossing (N : ℕ) :
    ∃ n ≥ N, total a s ha n ≤ s ∧ s < total a s ha (n + 1) := by
  classical
  obtain ⟨L, hLN, hL⟩ := exists_below (s := s) ha N
  have hm : ∃ m, L ≤ m ∧ s < total a s ha m := exists_above (s := s) ha L
  let m := Nat.find hm
  have hspec : L ≤ m ∧ s < total a s ha m := Nat.find_spec hm
  have hLm : L < m := by
    by_contra h
    have he : m = L := by omega
    rw [he] at hspec
    linarith [hspec.2]
  have hp : m - 1 + 1 = m := by omega
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · apply le_of_not_gt
    intro h
    have hmin := Nat.find_min hm (show m - 1 < m by omega)
    exact hmin ⟨by omega, h⟩
  · simpa only [hp] using hspec.2

/-- Crossing overshoot is no larger than the final term of the crossing. -/
lemma upcrossing_error (n : ℕ) (hlo : total a s ha n ≤ s)
    (hhi : s < total a s ha (n + 1)) :
    |total a s ha (n + 1) - s| ≤ |a (index a s ha n)| := by
  rw [abs_of_pos (sub_pos.mpr hhi), total_succ]
  have h := le_abs_self (a (index a s ha n))
  linarith

/-- Intermediate sums stay in an error interval once all increments are small. -/
lemma step_close (ε : ℝ) (n : ℕ)
    (h : |total a s ha n - s| < ε) (ht : |a (index a s ha n)| < ε) :
    |total a s ha (n + 1) - s| < ε := by
  rw [total_succ]
  have h₁ := abs_lt.mp h
  have h₂ := abs_lt.mp ht
  have hd := direction (s := s) ha n
  apply abs_lt.mpr
  split_ifs at hd with hlo
  · constructor <;> linarith
  · have hhi : s < total a s ha n := lt_of_not_ge hlo
    constructor <;> linarith

lemma total_converges : RealSequenceConverges (total a s ha) s := by
  have hterm : RealSequenceConverges (fun n => a (index a s ha n)) 0 := by
    apply (realSequenceConverges_iff _ _).mpr
    exact ((realSequenceConverges_iff _ _).mp (real_series_term_limit a ha.1)).comp
      (index_injective (s := s) ha).nat_tendsto_atTop
  intro ε hε
  obtain ⟨N, hN⟩ := hterm ε hε
  obtain ⟨n, hn, hlo, hhi⟩ := exists_upcrossing (s := s) ha N
  have hsmall : ∀ k ≥ N, |a (index a s ha k)| < ε := by
    simpa only [sub_zero] using hN
  have hbase : |total a s ha (n + 1) - s| < ε :=
    (upcrossing_error ha n hlo hhi).trans_lt (hsmall n hn)
  refine ⟨n + 1, fun k hk => ?_⟩
  induction k, hk using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih => exact step_close ha ε k ih (hsmall k (by omega))

end FiniteRearrangement

/-- Every finite real target is the ordinary sum of a bijective rearrangement. -/
theorem real_conditional_finite_rearrangement (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) (s : ℝ) :
    ∃ π : Equiv.Perm ℕ, RealSeriesHasSum (fun n => a (π n)) s := by
  let π : Equiv.Perm ℕ := Equiv.ofBijective (FiniteRearrangement.index a s ha)
    ⟨FiniteRearrangement.index_injective ha, FiniteRearrangement.index_surjective ha⟩
  refine ⟨π, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := FiniteRearrangement.total_converges (s := s) ha ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h := hN (n + 1) (by omega)
  change |(∑ j ∈ Finset.range (n + 1), a (FiniteRearrangement.index a s ha j)) - s| < ε
  simpa only [FiniteRearrangement.total, FiniteRearrangement.sum_used] using h

end SingleVariableAnalysis
