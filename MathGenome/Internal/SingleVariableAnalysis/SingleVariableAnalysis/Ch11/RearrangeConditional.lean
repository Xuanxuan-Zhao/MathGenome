import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.FiniteRearrangement
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Limsup
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.RearrangeConditional

/-!
K03.11.rearrange_conditional (paper.tex:1097–1120).
Permutations realize both infinite limits and every prescribed pair of extended
lower and upper limits. All zero indices are covered by least-index priority.
-/
namespace SingleVariableAnalysis

open Filter
open scoped Topology BigOperators

/-- The tail-lattice definitions agree with the limits for every convergent
extended-real sequence; this does not require bounded real partial sums. -/
theorem sequence_extrema_of_tendsto (b : ℕ → ℝ) (x : EReal)
    (h : Tendsto (fun n => (b n : EReal)) atTop (𝓝 x)) :
    sequenceLiminf b = x ∧ sequenceLimsup b = x := by
  change (⨆ N, ⨅ n ≥ N, (b n : EReal)) = x ∧
    (⨅ N, ⨆ n ≥ N, (b n : EReal)) = x
  rw [← liminf_eq_iSup_iInf_of_nat, ← limsup_eq_iInf_iSup_of_nat]
  exact ⟨h.liminf_eq, h.limsup_eq⟩

theorem real_conditional_finite_diagonal_rearrangement (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) (s : ℝ) :
    ∃ π : Equiv.Perm ℕ,
      sequenceLiminf (realPartialSum (fun n => a (π n))) = (s : EReal) ∧
      sequenceLimsup (realPartialSum (fun n => a (π n))) = (s : EReal) := by
  obtain ⟨π, hπ⟩ := real_conditional_finite_rearrangement a ha s
  exact ⟨π, sequence_extrema_of_tendsto _ _
    (EReal.tendsto_coe.mpr ((realSequenceConverges_iff _ _).mp hπ))⟩

/-! A moving-threshold construction. The threshold counts the strictly negative
indices already used. Zero terms are eligible in both directions, and therefore
are covered by the same least-index priority argument as the other terms. -/
namespace RisingRearrangement

noncomputable section

variable (a : ℕ → ℝ) (ha : RealSeriesConditionallyConverges a)

/-- The height increases precisely when a strictly negative term is selected. -/
def height (F : Finset ℕ) : ℕ := by
  classical
  exact (F.filter (fun i => a i < 0)).card

def selected : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => insert
      (FiniteRearrangement.next a (height a (selected n) : ℝ) ha (selected n))
      (selected n)

def pick (n : ℕ) : ℕ :=
  FiniteRearrangement.next a (height a (selected a ha n) : ℝ) ha (selected a ha n)

def mass (b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ selected a ha n, b i

def total (n : ℕ) : ℝ := mass a ha a n

def level (n : ℕ) : ℕ := height a (selected a ha n)

variable {a}

lemma selected_succ (n : ℕ) :
    selected a ha (n + 1) = insert (pick a ha n) (selected a ha n) := rfl

lemma fresh (n : ℕ) : pick a ha n ∉ selected a ha n :=
  (FiniteRearrangement.next_spec a _ ha _).1

lemma selected_mono : Monotone (selected a ha) :=
  monotone_nat_of_le_succ fun _ => Finset.subset_insert _ _

lemma earlier_mem {m n : ℕ} (h : m < n) : pick a ha m ∈ selected a ha n :=
  selected_mono ha (Nat.succ_le_of_lt h) (Finset.mem_insert_self _ _)

lemma pick_injective : Function.Injective (pick a ha) := by
  intro m n he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact fresh ha n (he ▸ earlier_mem ha h)
  · exact fresh ha m (he.symm ▸ earlier_mem ha h)

lemma selected_image (n : ℕ) :
    selected a ha n = (Finset.range n).image (pick a ha) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih => rw [selected_succ, Finset.range_add_one, Finset.image_insert, ih]

lemma mass_eq (b : ℕ → ℝ) (n : ℕ) :
    mass a ha b n = ∑ j ∈ Finset.range n, b (pick a ha j) := by
  classical
  unfold mass
  rw [selected_image]
  exact Finset.sum_image fun _ _ _ _ h => pick_injective ha h

lemma mass_step (b : ℕ → ℝ) (n : ℕ) :
    mass a ha b (n + 1) = mass a ha b n + b (pick a ha n) := by
  classical
  unfold mass
  rw [selected_succ, Finset.sum_insert (fresh ha n), add_comm]

lemma total_step (n : ℕ) : total a ha (n + 1) = total a ha n + a (pick a ha n) :=
  mass_step ha a n

lemma mass_mono (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) : Monotone (mass a ha b) :=
  monotone_nat_of_le_succ fun n => by rw [mass_step]; exact le_add_of_nonneg_right (hb _)

lemma level_mono : Monotone (level a ha) := by
  classical
  intro n m hnm
  exact Finset.card_le_card (Finset.filter_subset_filter _ (selected_mono ha hnm))

lemma level_step (n : ℕ) :
    level a ha (n + 1) = level a ha n + if a (pick a ha n) < 0 then 1 else 0 := by
  classical
  unfold level height
  rw [selected_succ, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    exact fun hi => fresh ha n ((Finset.mem_filter.mp hi).1)
  · simp

lemma direction (n : ℕ) :
    if total a ha n ≤ (level a ha n : ℝ) then 0 ≤ a (pick a ha n)
    else a (pick a ha n) ≤ 0 :=
  (FiniteRearrangement.next_spec a _ ha _).2

lemma priority (n i : ℕ) (hi : i ∉ selected a ha n)
    (he : if total a ha n ≤ (level a ha n : ℝ) then 0 ≤ a i else a i ≤ 0) :
    pick a ha n ≤ i :=
  FiniteRearrangement.next_le a _ ha _ i hi he

/-- Least-index priority exhausts every index eligible on a whole tail. -/
lemma covers_eligible (i : ℕ)
    (he : ∃ N, ∀ n ≥ N,
      if total a ha n ≤ (level a ha n : ℝ) then 0 ≤ a i else a i ≤ 0) :
    i ∈ Set.range (pick a ha) := by
  classical
  by_contra hi
  obtain ⟨N, hN⟩ := he
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((pick_injective ha).nat_tendsto_atTop.eventually (eventually_ge_atTop (i + 1)))
  let n := max N M
  have hnot : i ∉ selected a ha n := by
    rw [selected_image]
    intro h
    obtain ⟨j, _, hji⟩ := Finset.mem_image.mp h
    exact hi ⟨j, hji⟩
  have hp := priority ha n i hnot (hN n (le_max_left _ _))
  have hq := hM n (le_max_right _ _)
  omega

/-- Bounded accumulated mass implies convergence of the original nonnegative
part, provided all of its nonzero terms have been covered. -/
lemma converges_of_mass_bounded (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, b i ≠ 0 → i ∈ Set.range (pick a ha))
    (hB : ∃ B : ℝ, ∀ n, mass a ha b n ≤ B) : RealSeriesConverges b := by
  obtain ⟨B, hB⟩ := hB
  have hg : Summable (fun n => b (pick a ha n)) :=
    summable_of_sum_range_le (fun _ => hb _) (fun n => by
      simpa only [← mass_eq ha b n] using hB n)
  have hz : ∀ i, i ∉ Set.range (pick a ha) → b i = 0 := by
    intro i hi
    by_contra h
    exact hi (hc i h)
  have hs := ((pick_injective ha).hasSum_iff hz).mp hg.hasSum
  refine ⟨∑' n, b (pick a ha n), (realSequenceConverges_iff _ _).mpr ?_⟩
  exact hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

lemma total_parts (n : ℕ) :
    total a ha n = mass a ha (positivePart a) n - mass a ha (negativePart a) n := by
  classical
  unfold total mass
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => (positive_negative_part_identities a i).2.2.1

lemma not_always_below :
    ¬ ∃ N, ∀ n ≥ N, total a ha n ≤ (level a ha n : ℝ) := by
  rintro ⟨N, hN⟩
  have hpos : ∀ n ≥ N, 0 ≤ a (pick a ha n) := by
    intro n hn
    simpa [hN n hn] using direction ha n
  have hc : ∀ n ≥ N, level a ha n = level a ha N ∧
      mass a ha (negativePart a) n = mass a ha (negativePart a) N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ n hn ih =>
      rw [level_step, mass_step, ite_eq_right (not_lt_of_ge (hpos n hn)),
        show negativePart a (pick a ha n) = 0 by simp [negativePart, hpos n hn]]
      simpa using ih
  apply (conditional_parts_not_convergent a ha).1
  apply converges_of_mass_bounded ha (positivePart a)
    (fun i => (positive_negative_part_identities a i).1)
  · intro i hi
    have hp : 0 ≤ a i := by
      by_contra h
      exact hi (by simp [positivePart, le_of_not_ge h])
    exact covers_eligible ha i ⟨N, fun n hn => by simp [hN n hn, hp]⟩
  · refine ⟨(level a ha N : ℝ) + mass a ha (negativePart a) N, fun n => ?_⟩
    have htail : ∀ k ≥ N, mass a ha (positivePart a) k ≤
        (level a ha N : ℝ) + mass a ha (negativePart a) N := by
      intro k hk
      have h := hN k hk
      rw [(hc k hk).1] at h
      have ht := total_parts ha k
      rw [(hc k hk).2] at ht
      linarith
    rcases le_total N n with hn | hn
    · exact htail n hn
    · exact (mass_mono ha _ (fun i => (positive_negative_part_identities a i).1) hn).trans
        (htail N le_rfl)

lemma not_always_above :
    ¬ ∃ N, ∀ n ≥ N, (level a ha n : ℝ) < total a ha n := by
  rintro ⟨N, hN⟩
  have hneg : ∀ n ≥ N, a (pick a ha n) ≤ 0 := by
    intro n hn
    simpa [not_le_of_gt (hN n hn)] using direction ha n
  have hc : ∀ n ≥ N,
      mass a ha (positivePart a) n = mass a ha (positivePart a) N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [mass_step, show positivePart a (pick a ha n) = 0 by
        simp [positivePart, hneg n hn], add_zero, ih]
  apply (conditional_parts_not_convergent a ha).2
  apply converges_of_mass_bounded ha (negativePart a)
    (fun i => (positive_negative_part_identities a i).2.1)
  · intro i hi
    have hn : a i ≤ 0 := by
      by_contra h
      have hp := lt_of_not_ge h
      exact hi (by simp [negativePart, hp.le])
    exact covers_eligible ha i ⟨N, fun n hn' => by simp [not_le_of_gt (hN n hn'), hn]⟩
  · refine ⟨mass a ha (positivePart a) N, fun n => ?_⟩
    have htail : ∀ k ≥ N, mass a ha (negativePart a) k ≤ mass a ha (positivePart a) N := by
      intro k hk
      have h := hN k hk
      have hl : (0 : ℝ) ≤ (level a ha k : ℝ) := Nat.cast_nonneg _
      have ht := total_parts ha k
      rw [hc k hk] at ht
      linarith
    rcases le_total N n with hn | hn
    · exact htail n hn
    · exact (mass_mono ha _ (fun i => (positive_negative_part_identities a i).2.1) hn).trans
        (htail N le_rfl)

/-- Each sign is selected at arbitrarily late times; the moving threshold
cannot trap the construction on one side. -/
lemma exists_below (N : ℕ) : ∃ n ≥ N, total a ha n ≤ (level a ha n : ℝ) := by
  by_contra h
  push Not at h
  exact not_always_above ha ⟨N, h⟩

lemma exists_above (N : ℕ) : ∃ n ≥ N, (level a ha n : ℝ) < total a ha n := by
  by_contra h
  push Not at h
  exact not_always_below ha ⟨N, h⟩

/-- This includes every zero index: such an index is always eligible. -/
lemma pick_surjective : Function.Surjective (pick a ha) := by
  classical
  intro i
  by_contra hi
  have hnot : i ∉ Set.range (pick a ha) := hi
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((pick_injective ha).nat_tendsto_atTop.eventually (eventually_ge_atTop (i + 1)))
  have hprio : ∀ n ≥ M,
      (if total a ha n ≤ (level a ha n : ℝ) then 0 ≤ a i else a i ≤ 0) → False := by
    intro n hn he
    have hu : i ∉ selected a ha n := by
      rw [selected_image]
      intro h
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      exact hnot ⟨j, hj⟩
    have hp := priority ha n i hu he
    have hq := hM n hn
    omega
  rcases le_total 0 (a i) with hp | hn
  · obtain ⟨n, hn, hlow⟩ := exists_below ha M
    exact hprio n hn (by simp [hlow, hp])
  · obtain ⟨n, hn, hhigh⟩ := exists_above ha M
    exact hprio n hn (by simp [not_le_of_gt hhigh, ‹a i ≤ 0›])

lemma finite_covered (F : Finset ℕ) : ∃ N, F ⊆ selected a ha N := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert i F hi ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨j, rfl⟩ := pick_surjective ha i
    refine ⟨max N (j + 1), Finset.insert_subset ?_ ?_⟩
    · exact selected_mono ha (le_max_right _ _) (earlier_mem ha (Nat.lt_succ_self _))
    · exact hN.trans (selected_mono ha (le_max_left _ _))

lemma level_unbounded (K : ℕ) : ∃ N, K ≤ level a ha N := by
  classical
  obtain ⟨F, hF, hcard⟩ := (conditional_sign_sets_infinite a ha).2.exists_subset_card_eq K
  obtain ⟨N, hN⟩ := finite_covered ha F
  refine ⟨N, ?_⟩
  rw [← hcard]
  exact Finset.card_le_card (show F ⊆ (selected a ha N).filter (fun i => a i < 0) from
    fun i hi => Finset.mem_filter.mpr ⟨hN hi, hF hi⟩)

/-- Once the threshold is large and all unused increments are small, every
subsequent partial sum stays above a given bound. -/
lemma total_diverges : DivergesToPosInfinity (total a ha) := by
  have hterm : RealSequenceConverges (fun n => a (pick a ha n)) 0 := by
    apply (realSequenceConverges_iff _ _).mpr
    exact ((realSequenceConverges_iff _ _).mp (real_series_term_limit a ha.1)).comp
      (pick_injective ha).nat_tendsto_atTop
  intro B
  obtain ⟨K, hK⟩ := exists_nat_gt (B + 1)
  obtain ⟨N, hN⟩ := level_unbounded ha K
  obtain ⟨M, hM⟩ := hterm 1 zero_lt_one
  obtain ⟨n, hn, hhigh⟩ := exists_above ha (max N M)
  have hl : ∀ k ≥ n, B + 1 < (level a ha k : ℝ) := by
    intro k hk
    exact hK.trans_le (Nat.cast_le.mpr (hN.trans (level_mono ha (by omega))))
  have ht : ∀ k ≥ n, -1 < a (pick a ha k) := by
    intro k hk
    have h := hM k (by omega)
    simpa only [sub_zero] using (abs_lt.mp h).1
  refine ⟨n, fun k hk => ?_⟩
  induction k, hk using Nat.le_induction with
  | base => linarith [hl n le_rfl]
  | succ k hk ih =>
    change B < total a ha (k + 1)
    rw [total_step]
    have hd := direction ha k
    split_ifs at hd with hlo
    · linarith
    · have hhi : (level a ha k : ℝ) < total a ha k := lt_of_not_ge hlo
      linarith [hl k hk, ht k hk]

end
end RisingRearrangement

/-- A bijection of all original indices whose entire sequence of partial sums
tends to positive infinity. -/
theorem real_conditional_positive_infinity_rearrangement (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    ∃ π : Equiv.Perm ℕ, DivergesToPosInfinity (realPartialSum (fun n => a (π n))) := by
  let π : Equiv.Perm ℕ := Equiv.ofBijective (RisingRearrangement.pick a ha)
    ⟨RisingRearrangement.pick_injective ha, RisingRearrangement.pick_surjective ha⟩
  refine ⟨π, fun B => ?_⟩
  obtain ⟨N, hN⟩ := RisingRearrangement.total_diverges ha B
  refine ⟨N, fun n hn => ?_⟩
  have h := hN (n + 1) (by omega)
  change B < ∑ j ∈ Finset.range (n + 1), a (RisingRearrangement.pick a ha j)
  simpa only [RisingRearrangement.total, RisingRearrangement.mass_eq] using h

/-- Negating the terms preserves ordinary conditional convergence. -/
theorem real_conditional_neg (a : ℕ → ℝ) (ha : RealSeriesConditionallyConverges a) :
    RealSeriesConditionallyConverges (fun n => -a n) := by
  obtain ⟨S, hS⟩ := ha.1
  constructor
  · refine ⟨-S, ?_⟩
    have h := real_series_const_mul a S hS (-1)
    simpa only [neg_one_mul] using h
  · intro h
    apply ha.2
    simpa only [RealSeriesAbsolutelyConverges, abs_neg] using h

/-- Reverse signs in the positive-infinity construction. -/
theorem real_conditional_negative_infinity_rearrangement (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    ∃ π : Equiv.Perm ℕ, DivergesToNegInfinity (realPartialSum (fun n => a (π n))) := by
  obtain ⟨π, hπ⟩ := real_conditional_positive_infinity_rearrangement
    (fun n => -a n) (real_conditional_neg a ha)
  refine ⟨π, fun B => ?_⟩
  obtain ⟨N, hN⟩ := hπ (-B)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  dsimp [realPartialSum] at *
  rw [Finset.sum_neg_distrib] at h
  linarith

/-- Equal infinite endpoints are obtained as limits, not just as unbounded
subsequences of partial sums. -/
theorem real_conditional_top_diagonal_rearrangement (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    ∃ π : Equiv.Perm ℕ,
      sequenceLiminf (realPartialSum (fun n => a (π n))) = ⊤ ∧
      sequenceLimsup (realPartialSum (fun n => a (π n))) = ⊤ := by
  obtain ⟨π, hπ⟩ := real_conditional_positive_infinity_rearrangement a ha
  exact ⟨π, sequence_extrema_of_tendsto _ _
    (EReal.tendsto_coe_nhds_top_iff.mpr ((divergesToPosInfinity_iff _).mp hπ))⟩

theorem real_conditional_bot_diagonal_rearrangement (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    ∃ π : Equiv.Perm ℕ,
      sequenceLiminf (realPartialSum (fun n => a (π n))) = ⊥ ∧
      sequenceLimsup (realPartialSum (fun n => a (π n))) = ⊥ := by
  obtain ⟨π, hπ⟩ := real_conditional_negative_infinity_rearrangement a ha
  exact ⟨π, sequence_extrema_of_tendsto _ _
    (EReal.tendsto_coe_nhds_bot_iff.mpr ((divergesToNegInfinity_iff _).mp hπ))⟩

/-- Every equal pair of extended endpoints is realized, including both infinities. -/
theorem real_conditional_diagonal_rearrangement (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) (x : EReal) :
    ∃ π : Equiv.Perm ℕ,
      sequenceLiminf (realPartialSum (fun n => a (π n))) = x ∧
      sequenceLimsup (realPartialSum (fun n => a (π n))) = x := by
  induction x using EReal.rec with
  | bot => exact real_conditional_bot_diagonal_rearrangement a ha
  | coe x => exact real_conditional_finite_diagonal_rearrangement a ha x
  | top => exact real_conditional_top_diagonal_rearrangement a ha


/-! Alternating separated levels. Phase changes are made only after an actual
term has been inserted. The levels may be constant or tend to an infinity. -/
namespace AlternatingRearrangement
noncomputable section
attribute [local instance] Classical.propDecidable

variable (a : ℕ → ℝ) (ha : RealSeriesConditionallyConverges a)
variable (u v : ℕ → ℝ)

def target (k : ℕ) : ℝ := if k % 2 = 0 then v k else u k

def crosses (k : ℕ) (x : ℝ) : Prop := if k % 2 = 0 then v k < x else x ≤ u k

noncomputable def state : ℕ → Finset ℕ × ℕ
  | 0 => (∅, 0)
  | n + 1 => by
      classical
      let F := (state n).1
      let k := (state n).2
      let i := FiniteRearrangement.next a (target u v k) ha F
      let G := insert i F
      exact (G, if crosses u v k (∑ j ∈ G, a j) then k + 1 else k)

def used (n : ℕ) := (state a ha u v n).1
def phase (n : ℕ) := (state a ha u v n).2
def index (n : ℕ) := FiniteRearrangement.next a (target u v (phase a ha u v n)) ha
  (used a ha u v n)
def total (n : ℕ) : ℝ := ∑ i ∈ used a ha u v n, a i

variable {a u v}

lemma used_succ (n : ℕ) : used a ha u v (n+1) =
    insert (index a ha u v n) (used a ha u v n) := rfl
lemma phase_succ (n : ℕ) : phase a ha u v (n+1) =
    if crosses u v (phase a ha u v n) (total a ha u v (n+1))
    then phase a ha u v n + 1 else phase a ha u v n := rfl
lemma fresh (n : ℕ) : index a ha u v n ∉ used a ha u v n :=
  (FiniteRearrangement.next_spec a _ ha _).1
lemma used_mono : Monotone (used a ha u v) :=
  monotone_nat_of_le_succ fun _ => Finset.subset_insert _ _
lemma index_mem {m n : ℕ} (h : m < n) : index a ha u v m ∈ used a ha u v n :=
  used_mono ha (Nat.succ_le_of_lt h) (Finset.mem_insert_self _ _)
lemma index_injective : Function.Injective (index a ha u v) := by
  intro m n he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact fresh ha n (he ▸ index_mem ha h)
  · exact fresh ha m (he.symm ▸ index_mem ha h)
lemma used_image (n : ℕ) : used a ha u v n =
    (Finset.range n).image (index a ha u v) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih => rw [used_succ, Finset.range_add_one, Finset.image_insert, ih]
lemma sum_used (b : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ used a ha u v n, b i) = ∑ j ∈ Finset.range n, b (index a ha u v j) := by
  classical
  rw [used_image]
  exact Finset.sum_image fun _ _ _ _ h => index_injective ha h
lemma sum_step (b : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ used a ha u v (n+1), b i) =
      (∑ i ∈ used a ha u v n, b i) + b (index a ha u v n) := by
  classical
  rw [used_succ, Finset.sum_insert (fresh ha n), add_comm]
lemma total_step (n : ℕ) : total a ha u v (n+1) =
    total a ha u v n + a (index a ha u v n) := sum_step ha a n
lemma direction (n : ℕ) :
    if total a ha u v n ≤ target u v (phase a ha u v n)
    then 0 ≤ a (index a ha u v n) else a (index a ha u v n) ≤ 0 :=
  (FiniteRearrangement.next_spec a _ ha _).2
lemma priority (n i : ℕ) (hi : i ∉ used a ha u v n)
    (he : if total a ha u v n ≤ target u v (phase a ha u v n)
      then 0 ≤ a i else a i ≤ 0) : index a ha u v n ≤ i :=
  FiniteRearrangement.next_le a _ ha _ i hi he
lemma phase_mono : Monotone (phase a ha u v) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [phase_succ]
  split_ifs <;> omega
lemma phase_step_le (n : ℕ) : phase a ha u v (n+1) ≤ phase a ha u v n + 1 := by
  rw [phase_succ]
  split_ifs <;> omega
lemma phase_le (n : ℕ) : phase a ha u v n ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (phase_step_le ha n).trans (by omega)

variable (hu : Antitone u) (hv : Monotone v) (huv : ∀ k, u k < v k)
include hu hv huv

/-- After the first insertion the current sum lies on the appropriate side of
its active target. Separation and monotonicity justify phase transitions. -/
lemma active (n : ℕ) (hn : 1 ≤ n) :
    if phase a ha u v n % 2 = 0 then total a ha u v n ≤ v (phase a ha u v n)
    else u (phase a ha u v n) < total a ha u v n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [phase_succ]
  by_cases hc : crosses u v (phase a ha u v m) (total a ha u v (m+1))
  · rw [ite_eq_left hc]
    by_cases he : (phase a ha u v m + 1) % 2 = 0
    · rw [ite_eq_left he]
      have he' : phase a ha u v m % 2 ≠ 0 := by omega
      have hx : total a ha u v (m+1) ≤ u (phase a ha u v m) := by
        simpa [crosses, he'] using hc
      exact hx.trans ((huv _).le.trans (hv (Nat.le_succ _)))
    · rw [ite_eq_right he]
      have he' : phase a ha u v m % 2 = 0 := by omega
      have hx : v (phase a ha u v m) < total a ha u v (m+1) := by
        simpa [crosses, he'] using hc
      exact (hu (Nat.le_succ _)).trans_lt ((huv _).trans hx)
  · rw [ite_eq_right hc]
    by_cases he : phase a ha u v m % 2 = 0
    · rw [ite_eq_left he]
      exact le_of_not_gt (by simpa [crosses, he] using hc)
    · rw [ite_eq_right he]
      exact lt_of_not_ge (by simpa [crosses, he] using hc)

lemma phase_direction (n : ℕ) (hn : 1 ≤ n) :
    if phase a ha u v n % 2 = 0 then 0 ≤ a (index a ha u v n)
    else a (index a ha u v n) ≤ 0 := by
  have h := active ha hu hv huv n hn
  have hd := direction (u := u) (v := v) ha n
  by_cases he : phase a ha u v n % 2 = 0
  · simp only [he, ↓reduceIte] at h ⊢
    simpa [target, he, h] using hd
  · simp only [he, ↓reduceIte] at h ⊢
    simpa [target, he, not_le_of_gt h] using hd


omit hu hv huv in
lemma covers_eligible (i : ℕ)
    (he : ∃ N, ∀ n ≥ N,
      if total a ha u v n ≤ target u v (phase a ha u v n)
      then 0 ≤ a i else a i ≤ 0) : i ∈ Set.range (index a ha u v) := by
  by_contra hi
  obtain ⟨N, hN⟩ := he
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((index_injective (u := u) (v := v) ha).nat_tendsto_atTop.eventually
      (eventually_ge_atTop (i+1)))
  let n := max N M
  have hu' : i ∉ used a ha u v n := by
    rw [used_image]
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    exact hi ⟨j, hj⟩
  have hp := priority ha n i hu' (hN n (le_max_left _ _))
  have hq := hM n (le_max_right _ _)
  omega

omit hu hv huv in
lemma bounded_part_converges (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, b i ≠ 0 → i ∈ Set.range (index a ha u v))
    (hB : ∃ B : ℝ, ∀ n, (∑ i ∈ used a ha u v n, b i) ≤ B) :
    RealSeriesConverges b := by
  obtain ⟨B, hB⟩ := hB
  have hs : Summable (b ∘ index a ha u v) :=
    summable_of_sum_range_le (fun _ => hb _) (fun n => by
      simpa only [Function.comp_apply, ← sum_used ha b n] using hB n)
  have hb0 : ∀ i, i ∉ Set.range (index a ha u v) → b i = 0 :=
    fun i hi => by_contra fun h => hi (hc i h)
  have hs' := ((index_injective ha).hasSum_iff hb0).mp hs.hasSum
  exact ⟨_, (realSequenceConverges_iff _ _).mpr
    (hs'.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))⟩

omit hu hv huv in
lemma sum_mono (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) :
    Monotone (fun n => ∑ i ∈ used a ha u v n, b i) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [sum_step]
  exact le_add_of_nonneg_right (hb _)

lemma phase_not_constant (N k : ℕ) (hN : ∀ n ≥ N, phase a ha u v n = k) : False := by
  let M := max N 1
  have hp : ∀ n ≥ M, phase a ha u v n = k := fun n hn => hN n (by omega)
  have hact : ∀ n ≥ M,
      if k % 2 = 0 then total a ha u v n ≤ v k else u k < total a ha u v n := by
    intro n hn
    simpa only [hp n hn] using active ha hu hv huv n (by omega)
  have hdir : ∀ n ≥ M,
      if k % 2 = 0 then 0 ≤ a (index a ha u v n) else a (index a ha u v n) ≤ 0 := by
    intro n hn
    simpa only [hp n hn] using phase_direction ha hu hv huv n (by omega)
  have hparts (n : ℕ) : total a ha u v n =
      (∑ i ∈ used a ha u v n, positivePart a i) -
        (∑ i ∈ used a ha u v n, negativePart a i) := by
    unfold total
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (positive_negative_part_identities a i).2.2.1
  by_cases he : k % 2 = 0
  · have hpos : ∀ n ≥ M, 0 ≤ a (index a ha u v n) := by simpa [he] using hdir
    have hQ : ∀ n ≥ M, (∑ i ∈ used a ha u v n, negativePart a i) =
        ∑ i ∈ used a ha u v M, negativePart a i := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih => rw [sum_step, ih]; simp [negativePart, hpos n hn]
    apply (conditional_parts_not_convergent a ha).1
    apply bounded_part_converges (u := u) (v := v) ha (positivePart a)
      (fun i => (positive_negative_part_identities a i).1)
    · intro i hi
      have hai : 0 ≤ a i := by
        by_contra h
        exact hi (by simp [positivePart, le_of_not_ge h])
      refine covers_eligible (u := u) (v := v) ha i ⟨M, fun n hn => ?_⟩
      have hx : total a ha u v n ≤ target u v (phase a ha u v n) := by
        simpa [target, hp n hn, he] using hact n hn
      simp [hx, hai]
    · have hb : ∀ n ≥ M, (∑ i ∈ used a ha u v n, positivePart a i) ≤
          v k + ∑ i ∈ used a ha u v M, negativePart a i := by
        intro n hn
        have ht : total a ha u v n ≤ v k := by simpa [he] using hact n hn
        have hid := hparts n
        rw [hQ n hn] at hid
        linarith
      refine ⟨v k + ∑ i ∈ used a ha u v M, negativePart a i, fun n => ?_⟩
      rcases le_total M n with hn | hn
      · exact hb n hn
      · exact (sum_mono ha _ (fun i => (positive_negative_part_identities a i).1) hn).trans
          (hb M le_rfl)
  · have hneg : ∀ n ≥ M, a (index a ha u v n) ≤ 0 := by simpa [he] using hdir
    have hP : ∀ n ≥ M, (∑ i ∈ used a ha u v n, positivePart a i) =
        ∑ i ∈ used a ha u v M, positivePart a i := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih => rw [sum_step, ih]; simp [positivePart, hneg n hn]
    apply (conditional_parts_not_convergent a ha).2
    apply bounded_part_converges (u := u) (v := v) ha (negativePart a)
      (fun i => (positive_negative_part_identities a i).2.1)
    · intro i hi
      have hai : a i ≤ 0 := by
        by_contra h
        exact hi (by simp [negativePart, (lt_of_not_ge h).le])
      refine covers_eligible (u := u) (v := v) ha i ⟨M, fun n hn => ?_⟩
      have hx : target u v (phase a ha u v n) < total a ha u v n := by
        simpa [target, hp n hn, he] using hact n hn
      simp [not_le_of_gt hx, hai]
    · have hb : ∀ n ≥ M, (∑ i ∈ used a ha u v n, negativePart a i) ≤
          (∑ i ∈ used a ha u v M, positivePart a i) - u k := by
        intro n hn
        have ht : u k < total a ha u v n := by simpa [he] using hact n hn
        have hid := hparts n
        rw [hP n hn] at hid
        linarith
      refine ⟨(∑ i ∈ used a ha u v M, positivePart a i) - u k, fun n => ?_⟩
      rcases le_total M n with hn | hn
      · exact hb n hn
      · exact (sum_mono ha _ (fun i => (positive_negative_part_identities a i).2.1) hn).trans
          (hb M le_rfl)

/-- Every phase ends after finitely many insertions. -/
lemma phase_unbounded (K : ℕ) : ∃ n, K ≤ phase a ha u v n := by
  by_contra h
  push Not at h
  have hs : Set.Finite (Set.range (phase a ha u v)) :=
    (Set.finite_Iio K).subset (by rintro _ ⟨n, rfl⟩; exact h n)
  obtain ⟨k, hk, hmax⟩ := hs.bddAbove.exists_isGreatest_of_nonempty (Set.range_nonempty _)
  obtain ⟨N, rfl⟩ := hk
  apply phase_not_constant ha hu hv huv N (phase a ha u v N)
  intro n hn
  exact le_antisymm (hmax (Set.mem_range_self n)) (phase_mono ha hn)

lemma phase_tendsto : Tendsto (phase a ha u v) atTop atTop :=
  tendsto_atTop_atTop.mpr fun K => by
    obtain ⟨N, hN⟩ := phase_unbounded ha hu hv huv K
    exact ⟨N, fun n hn => hN.trans (phase_mono ha hn)⟩

/-- Unit-size phase increments ensure that no phase is skipped. -/
lemma phase_hits (K : ℕ) : ∃ n, phase a ha u v n = K := by
  have hex := phase_unbounded ha hu hv huv K
  let n := Nat.find hex
  have hn : K ≤ phase a ha u v n := Nat.find_spec hex
  refine ⟨n, le_antisymm ?_ hn⟩
  by_cases hn0 : n = 0
  · simpa [hn0, phase, state] using (Nat.zero_le K)
  · have hprev : phase a ha u v (n-1) < K := by
      exact lt_of_not_ge (Nat.find_min hex (by omega))
    have hstep := phase_step_le (u := u) (v := v) ha (n-1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hstep
    omega


lemma phase_entry (k : ℕ) : ∃ n, phase a ha u v n = k ∧
    phase a ha u v (n+1) = k+1 := by
  have hex := phase_unbounded ha hu hv huv (k+1)
  let m := Nat.find hex
  have hm : k+1 ≤ phase a ha u v m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h
    have hp := phase_le (u := u) (v := v) ha m
    omega
  have hprev : phase a ha u v (m-1) < k+1 :=
    lt_of_not_ge (Nat.find_min hex (by omega))
  have hstep := phase_step_le (u := u) (v := v) ha (m-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hstep
  refine ⟨m-1, by omega, ?_⟩
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  omega

lemma entry_crosses {n k : ℕ} (hk : phase a ha u v n = k)
    (hk' : phase a ha u v (n+1) = k+1) : crosses u v k (total a ha u v (n+1)) := by
  have h := phase_succ (u := u) (v := v) ha n
  rw [hk, hk'] at h
  split_ifs at h with hc
  · exact hc
  · omega

/-- Least-index priority in the infinitely many phases of each parity includes
all positive, negative and zero indices. -/
lemma index_surjective : Function.Surjective (index a ha u v) := by
  intro i
  by_contra hi
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((index_injective (u := u) (v := v) ha).nat_tendsto_atTop.eventually
      (eventually_ge_atTop (i+1)))
  have hbad : ∀ n ≥ M,
      (if total a ha u v n ≤ target u v (phase a ha u v n)
        then 0 ≤ a i else a i ≤ 0) → False := by
    intro n hn he
    have hu' : i ∉ used a ha u v n := by
      rw [used_image]
      intro h
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      exact hi ⟨j, hj⟩
    have hp := priority ha n i hu' he
    have hq := hM n hn
    omega
  rcases le_total 0 (a i) with hai | hai
  · obtain ⟨n, hn, _⟩ := phase_entry ha hu hv huv (2*(M+1))
    have hle := phase_le (u := u) (v := v) ha n
    have he : phase a ha u v n % 2 = 0 := by omega
    have hx : total a ha u v n ≤ target u v (phase a ha u v n) := by
      simpa [he, target] using active ha hu hv huv n (by omega)
    exact hbad n (by omega) (by simp [hx, hai])
  · obtain ⟨n, hn, _⟩ := phase_entry ha hu hv huv (2*(M+1)+1)
    have hle := phase_le (u := u) (v := v) ha n
    have he : phase a ha u v n % 2 ≠ 0 := by omega
    have hx : target u v (phase a ha u v n) < total a ha u v n := by
      simpa [he, target] using active ha hu hv huv n (by omega)
    exact hbad n (by omega) (by simp [not_le_of_gt hx, hai])

lemma terms_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, |a (index a ha u v n)| < ε := by
  have ht := ((realSequenceConverges_iff _ _).mp (real_series_term_limit a ha.1)).comp
    (index_injective (u := u) (v := v) ha).nat_tendsto_atTop
  simpa only [SequenceEventually, sub_zero, Function.comp_apply] using
    ((realSequenceConverges_iff _ _).mpr ht) ε hε

/-- A lower bound on late lower levels is inherited by every intermediate sum,
up to the size of one late increment. -/
lemma eventually_above (c d : ℝ) (hcd : c < d)
    (hd : ∃ K, ∀ k ≥ K, d ≤ u k) : ∃ N, ∀ n ≥ N, c < total a ha u v n := by
  obtain ⟨K, hK⟩ := hd
  obtain ⟨M, hM⟩ := terms_small ha hu hv huv (d-c) (sub_pos.mpr hcd)
  obtain ⟨n, hn, hn'⟩ := phase_entry ha hu hv huv (2*(max K M+1))
  have hle := phase_le (u := u) (v := v) ha n
  have hn1 : 1 ≤ n := by omega
  have he : (2*(max K M+1)) % 2 = 0 := by omega
  have hx : v (2*(max K M+1)) < total a ha u v (n+1) := by
    simpa only [crosses, he, ↓reduceIte] using entry_crosses ha hu hv huv hn hn'
  have hbase : c < total a ha u v (n+1) :=
    hcd.trans_le ((hK _ (by omega)).trans ((huv _).le.trans hx.le))
  refine ⟨n+1, fun m hm => ?_⟩
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    have hp : K ≤ phase a ha u v m := by
      have ht := phase_mono (u := u) (v := v) ha (show n ≤ m by omega)
      omega
    have ht := abs_lt.mp (hM m (by omega))
    have hdir := phase_direction ha hu hv huv m (by omega)
    have hact := active ha hu hv huv m (by omega)
    rw [total_step]
    by_cases hpar : phase a ha u v m % 2 = 0
    · simp only [hpar, ↓reduceIte] at hdir
      linarith
    · simp only [hpar, ↓reduceIte] at hact
      linarith [hK _ hp]

lemma eventually_below (c d : ℝ) (hdc : d < c)
    (hd : ∃ K, ∀ k ≥ K, v k ≤ d) : ∃ N, ∀ n ≥ N, total a ha u v n < c := by
  obtain ⟨K, hK⟩ := hd
  obtain ⟨M, hM⟩ := terms_small ha hu hv huv (c-d) (sub_pos.mpr hdc)
  obtain ⟨n, hn, hn'⟩ := phase_entry ha hu hv huv (2*(max K M+1)+1)
  have hle := phase_le (u := u) (v := v) ha n
  have he : (2*(max K M+1)+1) % 2 ≠ 0 := by omega
  have hx : total a ha u v (n+1) ≤ u (2*(max K M+1)+1) := by
    simpa only [crosses, he, ↓reduceIte] using entry_crosses ha hu hv huv hn hn'
  have hbase : total a ha u v (n+1) < c :=
    hx.trans_lt ((huv _).trans_le (hK _ (by omega)) |>.trans hdc)
  refine ⟨n+1, fun m hm => ?_⟩
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    have hp : K ≤ phase a ha u v m := by
      have ht := phase_mono (u := u) (v := v) ha (show n ≤ m by omega)
      omega
    have ht := abs_lt.mp (hM m (by omega))
    have hdir := phase_direction ha hu hv huv m (by omega)
    have hact := active ha hu hv huv m (by omega)
    rw [total_step]
    by_cases hpar : phase a ha u v m % 2 = 0
    · simp only [hpar, ↓reduceIte] at hact
      linarith [hK _ hp]
    · simp only [hpar, ↓reduceIte] at hdir
      linarith

lemma frequently_below (c : ℝ) (hc : ∃ K, ∀ k ≥ K, u k < c) :
    ∀ N, ∃ n ≥ N, total a ha u v n < c := by
  obtain ⟨K, hK⟩ := hc
  intro N
  obtain ⟨n, hn, hn'⟩ := phase_entry ha hu hv huv (2*(max K N+1)+1)
  have hle := phase_le (u := u) (v := v) ha n
  have he : (2*(max K N+1)+1) % 2 ≠ 0 := by omega
  have hx : total a ha u v (n+1) ≤ u (2*(max K N+1)+1) := by
    simpa only [crosses, he, ↓reduceIte] using entry_crosses ha hu hv huv hn hn'
  exact ⟨n+1, by omega, hx.trans_lt (hK _ (by omega))⟩

lemma frequently_above (c : ℝ) (hc : ∃ K, ∀ k ≥ K, c < v k) :
    ∀ N, ∃ n ≥ N, c < total a ha u v n := by
  obtain ⟨K, hK⟩ := hc
  intro N
  obtain ⟨n, hn, hn'⟩ := phase_entry ha hu hv huv (2*(max K N+1))
  have hle := phase_le (u := u) (v := v) ha n
  have he : (2*(max K N+1)) % 2 = 0 := by omega
  have hx : v (2*(max K N+1)) < total a ha u v (n+1) := by
    simpa only [crosses, he, ↓reduceIte] using entry_crosses ha hu hv huv hn hn'
  exact ⟨n+1, by omega, (hK _ (by omega)).trans hx⟩

end
end AlternatingRearrangement




/-- Real cuts characterize the extended tail extrema without boundedness. -/
theorem sequence_extrema_of_cuts (b : ℕ → ℝ) (α β : EReal)
    (hlo : ∀ c : ℝ, (c : EReal) < α → ∃ N, ∀ n ≥ N, c < b n)
    (hlof : ∀ c : ℝ, α < (c : EReal) → ∀ N, ∃ n ≥ N, b n < c)
    (hhi : ∀ c : ℝ, β < (c : EReal) → ∃ N, ∀ n ≥ N, b n < c)
    (hhif : ∀ c : ℝ, (c : EReal) < β → ∀ N, ∃ n ≥ N, c < b n) :
    sequenceLiminf b = α ∧ sequenceLimsup b = β := by
  constructor <;> apply le_antisymm
  · by_contra h
    obtain ⟨c, hα, hc⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    have hl : sequenceLiminf b ≤ (c : EReal) := by
      apply iSup_le
      intro N
      obtain ⟨n, hn, hbn⟩ := hlof c hα N
      exact (iInf_le_of_le n (iInf_le_of_le hn le_rfl)).trans
        (EReal.coe_le_coe hbn.le)
    exact not_le_of_gt hc hl
  · by_contra h
    obtain ⟨c, hc, hα⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    obtain ⟨N, hN⟩ := hlo c hα
    have hl : (c : EReal) ≤ sequenceLiminf b := by
      exact (le_iInf fun n => le_iInf fun hn => EReal.coe_le_coe (hN n hn).le).trans
        (le_iSup (tailInfimum b) N)
    exact not_le_of_gt hc hl
  · by_contra h
    obtain ⟨c, hβ, hc⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    obtain ⟨N, hN⟩ := hhi c hβ
    have hl : sequenceLimsup b ≤ (c : EReal) := by
      exact (iInf_le (tailSupremum b) N).trans
        (iSup_le fun n => iSup_le fun hn => EReal.coe_le_coe (hN n hn).le)
    exact not_le_of_gt hc hl
  · by_contra h
    obtain ⟨c, hc, hβ⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    have hl : (c : EReal) ≤ sequenceLimsup b := by
      apply le_iInf
      intro N
      obtain ⟨n, hn, hbn⟩ := hhif c hβ N
      exact (EReal.coe_le_coe hbn.le).trans
        (le_iSup_of_le n (le_iSup_of_le hn le_rfl))
    exact not_le_of_gt hc hl

namespace AlternatingRearrangement
noncomputable section
variable (a : ℕ → ℝ) (ha : RealSeriesConditionallyConverges a)
variable (u v : ℕ → ℝ) (hu : Antitone u) (hv : Monotone v) (huv : ∀ k, u k < v k)

include ha hu hv huv

/-- Separated levels tending to the prescribed endpoints give a permutation
with precisely those extrema, including infinite endpoints. -/
theorem realizes_levels (α β : EReal)
    (hul : ∀ c : ℝ, (c : EReal) < α → ∃ K, ∀ k ≥ K, c < u k)
    (hur : ∀ c : ℝ, α < (c : EReal) → ∃ K, ∀ k ≥ K, u k < c)
    (hvl : ∀ c : ℝ, (c : EReal) < β → ∃ K, ∀ k ≥ K, c < v k)
    (hvr : ∀ c : ℝ, β < (c : EReal) → ∃ K, ∀ k ≥ K, v k < c) :
    ∃ π : Equiv.Perm ℕ,
      sequenceLiminf (realPartialSum (fun n => a (π n))) = α ∧
      sequenceLimsup (realPartialSum (fun n => a (π n))) = β := by
  let π : Equiv.Perm ℕ := Equiv.ofBijective (index a ha u v)
    ⟨index_injective ha, index_surjective ha hu hv huv⟩
  have heq (n : ℕ) : realPartialSum (fun n => a (π n)) n = total a ha u v (n+1) :=
    (sum_used ha a (n+1)).symm
  refine ⟨π, sequence_extrema_of_cuts _ α β ?_ ?_ ?_ ?_⟩
  · intro c hc
    obtain ⟨d, hcd, hd⟩ := EReal.exists_between_coe_real hc
    obtain ⟨K, hK⟩ := hul d hd
    obtain ⟨N, hN⟩ := eventually_above ha hu hv huv c d
      (EReal.coe_lt_coe_iff.mp hcd) ⟨K, fun k hk => (hK k hk).le⟩
    exact ⟨N, fun n hn => by rw [heq]; exact hN _ (by omega)⟩
  · intro c hc N
    obtain ⟨m, hm, hmc⟩ := frequently_below ha hu hv huv c (hur c hc) (N+1)
    refine ⟨m-1, by omega, ?_⟩
    rw [heq, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    exact hmc
  · intro c hc
    obtain ⟨d, hd, hdc⟩ := EReal.exists_between_coe_real hc
    obtain ⟨K, hK⟩ := hvr d hd
    obtain ⟨N, hN⟩ := eventually_below ha hu hv huv c d
      (EReal.coe_lt_coe_iff.mp hdc) ⟨K, fun k hk => (hK k hk).le⟩
    exact ⟨N, fun n hn => by rw [heq]; exact hN _ (by omega)⟩
  · intro c hc N
    obtain ⟨m, hm, hmc⟩ := frequently_above ha hu hv huv c (hvl c hc) (N+1)
    refine ⟨m-1, by omega, ?_⟩
    rw [heq, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    exact hmc

end
end AlternatingRearrangement


/-- A decreasing real sequence below a separating real point approaches any
extended lower endpoint other than positive infinity. -/
lemma exists_lower_levels (α : EReal) (c : ℝ) (hα : α < (c : EReal)) :
    ∃ u : ℕ → ℝ, Antitone u ∧ (∀ k, u k < c) ∧
      (∀ d : ℝ, (d : EReal) < α → ∃ K, ∀ k ≥ K, d < u k) ∧
      (∀ d : ℝ, α < (d : EReal) → ∃ K, ∀ k ≥ K, u k < d) := by
  induction α using EReal.rec with
  | bot =>
    refine ⟨fun k => c-1-k, ?_, ?_, ?_, ?_⟩
    · intro n m hnm
      have h := Nat.cast_le (α := ℝ).mpr hnm
      dsimp
      linarith
    · intro k
      have h := Nat.cast_nonneg (α := ℝ) k
      dsimp
      linarith
    · intro d hd
      exact (not_lt_bot hd).elim
    · intro d _
      obtain ⟨K, hK⟩ := exists_nat_gt (c-1-d)
      refine ⟨K, fun k hk => ?_⟩
      have h := Nat.cast_le (α := ℝ).mpr hk
      dsimp
      linarith
  | coe x =>
    refine ⟨fun _ => x, fun _ _ _ => le_rfl, fun _ => EReal.coe_lt_coe_iff.mp hα,
      fun d hd => ⟨0, fun _ _ => EReal.coe_lt_coe_iff.mp hd⟩,
      fun d hd => ⟨0, fun _ _ => EReal.coe_lt_coe_iff.mp hd⟩⟩
  | top => exact (not_lt_of_ge le_top hα).elim

/-- The dual upper levels, with a growing real sequence when the endpoint is
positive infinity. -/
lemma exists_upper_levels (β : EReal) (c : ℝ) (hβ : (c : EReal) < β) :
    ∃ v : ℕ → ℝ, Monotone v ∧ (∀ k, c < v k) ∧
      (∀ d : ℝ, (d : EReal) < β → ∃ K, ∀ k ≥ K, d < v k) ∧
      (∀ d : ℝ, β < (d : EReal) → ∃ K, ∀ k ≥ K, v k < d) := by
  induction β using EReal.rec with
  | bot => exact (not_lt_bot hβ).elim
  | coe x =>
    refine ⟨fun _ => x, fun _ _ _ => le_rfl, fun _ => EReal.coe_lt_coe_iff.mp hβ,
      fun d hd => ⟨0, fun _ _ => EReal.coe_lt_coe_iff.mp hd⟩,
      fun d hd => ⟨0, fun _ _ => EReal.coe_lt_coe_iff.mp hd⟩⟩
  | top =>
    refine ⟨fun k => c+1+k, ?_, ?_, ?_, ?_⟩
    · intro n m hnm
      dsimp
      exact add_le_add le_rfl (Nat.cast_le.mpr hnm)
    · intro k
      have h := Nat.cast_nonneg (α := ℝ) k
      dsimp
      linarith
    · intro d _
      obtain ⟨K, hK⟩ := exists_nat_gt (d-c-1)
      refine ⟨K, fun k hk => ?_⟩
      have h := Nat.cast_le (α := ℝ).mpr hk
      dsimp
      linarith
    · intro d hd
      exact (not_lt_of_ge le_top hd).elim

/-- The full extended Riemann rearrangement theorem for ordinary conditional
convergence. Zero indices are included by the priority construction. -/
theorem real_conditional_extended_rearrangement (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) (α β : EReal) (hαβ : α ≤ β) :
    ∃ π : Equiv.Perm ℕ,
      sequenceLiminf (realPartialSum (fun n => a (π n))) = α ∧
      sequenceLimsup (realPartialSum (fun n => a (π n))) = β := by
  rcases eq_or_lt_of_le hαβ with rfl | hlt
  · exact real_conditional_diagonal_rearrangement a ha _
  · obtain ⟨c, hα, hβ⟩ := EReal.exists_between_coe_real hlt
    obtain ⟨u, hu, huc, hul, hur⟩ := exists_lower_levels α c hα
    obtain ⟨v, hv, hcv, hvl, hvr⟩ := exists_upper_levels β c hβ
    exact AlternatingRearrangement.realizes_levels a ha u v hu hv
      (fun k => (huc k).trans (hcv k)) α β hul hur hvl hvr

end SingleVariableAnalysis
