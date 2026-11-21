import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.ExcursionMeasure
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.ClosedRecurrentClasses
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.StrongMarkov
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.DeterministicTransitions

open MeasureTheory Filter
open scoped ENNReal MeasureTheory Classical
set_option backward.isDefEq.respectTransparency false
universe u
namespace P207.Markov
noncomputable section

namespace ExcursionMeasure
abbrev excursionVisits : ExcursionMeasureSpec.excursionVisitsType := @P207.Markov.excursionVisits
abbrev excursionMass : ExcursionMeasureSpec.excursionMassType := @P207.Markov.excursionMass
abbrev normalizedExcursionMass : ExcursionMeasureSpec.normalizedExcursionMassType :=
  @P207.Markov.normalizedExcursionMass
end ExcursionMeasure

variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

local instance (P : StochasticMatrix S) (i : S) : IsProbabilityMeasure (statePathLaw P i) := by
  unfold statePathLaw
  infer_instance

theorem measurable_excursionVisits (i j : S) : Measurable (excursionVisits i j) := by
  classical
  apply Measurable.tsum
  intro n
  exact Measurable.ite
    ((measurableSet_lt measurable_const (measurable_returnTime i)).inter
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const))
    measurable_const measurable_const

omit [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- The return occurs after time zero, even on paths that never return. -/
theorem zero_lt_returnTime (i : S) (ω : ℕ → S) : (0 : WithTop ℕ) < returnTime i ω := by
  apply lt_of_not_ge
  intro h
  obtain ⟨k, hk, h0, _⟩ := (positiveReturnTime_le_iff coordinate i ω 0).mp h
  omega

omit [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem excursionVisits_self (i : S) (ω : ℕ → S) (h0 : ω 0 = i) :
    excursionVisits i i ω = 1 := by
  classical
  unfold excursionVisits
  rw [tsum_eq_single 0]
  · simp [zero_lt_returnTime, h0]
  · intro n hn
    apply ite_eq_right
    rintro ⟨hlt, heq⟩
    have hle := (positiveReturnTime_le_iff coordinate i ω n).mpr
      ⟨n, by omega, le_rfl, heq⟩
    exact (not_lt_of_ge hle) hlt

theorem excursionMass_self (P : StochasticMatrix S) (i : S) :
    excursionMass P i i = 1 := by
  unfold excursionMass
  calc
    (∫⁻ ω, excursionVisits i i ω ∂statePathLaw P i) = ∫⁻ _, 1 ∂statePathLaw P i := by
      apply lintegral_congr_ae
      filter_upwards [statePathLaw_initial P i] with ω hω
      exact excursionVisits_self i ω hω
    _ = 1 := by simp

omit [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- Tonelli for visits partitioned by their state. -/
theorem excursionVisits_total (i : S) (ω : ℕ → S) :
    ∑' j, excursionVisits i j ω = ENat.toENNReal (returnTime i ω) := by
  classical
  unfold excursionVisits
  rw [ENNReal.tsum_comm]
  have he (n : ℕ) : (∑' j : S,
      if (n : WithTop ℕ) < returnTime i ω ∧ ω n = j then (1 : ℝ≥0∞) else 0) =
      if (n : WithTop ℕ) < returnTime i ω then 1 else 0 := by
    by_cases hn : (n : WithTop ℕ) < returnTime i ω
    · simp [hn, eq_comm]
    · simp [hn]
  simp_rw [he]
  generalize returnTime i ω = t
  induction t using WithTop.recTopCoe with
  | top =>
    change (∑' n : ℕ, if (n : WithTop ℕ) < ⊤ then (1 : ℝ≥0∞) else 0) =
      ENat.toENNReal (⊤ : ℕ∞)
    simp
  | coe t =>
    change (∑' n : ℕ, if (n : WithTop ℕ) < (t : WithTop ℕ) then (1 : ℝ≥0∞) else 0) =
      ENat.toENNReal (t : ℕ∞)
    simp only [ENat.toENNReal_coe]
    rw [tsum_eq_sum (s := Finset.range t)]
    · trans ∑ _n ∈ Finset.range t, (1 : ℝ≥0∞)
      · apply Finset.sum_congr rfl
        intro n hn
        apply ite_eq_left
        exact_mod_cast (Finset.mem_range.mp hn)
      · simp
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      apply ite_eq_right
      apply not_lt.mpr
      exact_mod_cast hn

theorem excursionMass_total (P : StochasticMatrix S) (i : S) :
    ∑' j, excursionMass P i j = meanReturnTime P i := by
  unfold excursionMass meanReturnTime
  rw [← lintegral_tsum (fun j => (measurable_excursionVisits i j).aemeasurable)]
  exact lintegral_congr fun ω => excursionVisits_total i ω

/-- Survival up to time `n` is known at time `n`. -/
theorem measurableSet_excursionAlive (i : S) (n : ℕ) :
    MeasurableSet[coordinateFiltration n] {ω : ℕ → S | (n : WithTop ℕ) < returnTime i ω} := by
  simpa only [Set.compl_ofPred, not_le] using ((returnTime_isStoppingTime i) n).compl

theorem excursionMass_eq_tsum (P : StochasticMatrix S) (i j : S) :
    excursionMass P i j = ∑' n : ℕ,
      statePathLaw P i {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω n = j} := by
  classical
  unfold excursionMass excursionVisits
  have hm (n : ℕ) : MeasurableSet {ω : ℕ → S |
      (n : WithTop ℕ) < returnTime i ω ∧ ω n = j} :=
    (coordinateFiltration.le n _ (measurableSet_excursionAlive i n)).inter
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)
  rw [lintegral_tsum (fun n => (Measurable.ite (hm n) measurable_const measurable_const).aemeasurable)]
  apply tsum_congr
  intro n
  simpa [Set.indicator_apply] using
    (lintegral_indicator (μ := statePathLaw P i) (f := fun _ => (1 : ℝ≥0∞)) (hm n))

/-- One step of the chain on each surviving state layer. -/
theorem excursion_transition (P : StochasticMatrix S) (i j : S) (n : ℕ) :
    (∑' k, statePathLaw P i {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω n = k} * P k j) =
      statePathLaw P i {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω (n + 1) = j} := by
  let : Nonempty S := ⟨i⟩
  let A : S → Set (ℕ → S) := fun k =>
    {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω n = k}
  let B : Set (ℕ → S) := {ω | ω (n + 1) = j}
  have hA (k : S) : MeasurableSet[coordinateFiltration n] (A k) :=
    (measurableSet_excursionAlive i n).inter
      (measurableSet_eq_fun ((coordinate_isMarkovChain P (PMF.pure i)).1 n) measurable_const)
  have hB : MeasurableSet B := measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have he : {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω (n + 1) = j} =
      ⋃ k, A k ∩ B := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, A, B]
    exact ⟨fun h => ⟨ω n, ⟨h.1, rfl⟩, h.2⟩, fun ⟨_, h, hj⟩ => ⟨h.1, hj⟩⟩
  have hd : Pairwise (fun k l => Disjoint (A k ∩ B) (A l ∩ B)) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro ω hk hl
    exact hkl (hk.1.2.symm.trans hl.1.2)
  rw [he, measure_iUnion hd (fun k => (coordinateFiltration.le n _ (hA k)).inter hB)]
  apply tsum_congr
  intro k
  exact (FixedFutureLaw.event_step (coordinate_isMarkovChain P (PMF.pure i)) n
    (A k) (hA k) k j (fun ω hω => hω.2)).symm

/-- On a finite excursion the endpoints coincide, so shifting the visit sum
by one leaves it unchanged. No expectation is subtracted here. -/
theorem excursionVisits_shift (i j : S) (ω : ℕ → S) (h0 : ω 0 = i)
    (ht : returnTime i ω < ⊤) :
    (∑' n : ℕ, if (n : WithTop ℕ) < returnTime i ω ∧ ω (n + 1) = j
      then (1 : ℝ≥0∞) else 0) = excursionVisits i j ω := by
  classical
  obtain ⟨m, hm'⟩ := WithTop.ne_top_iff_exists.mp ht.ne
  have hm := hm'.symm
  have hmi := (returnTime_at_finite i ω m hm).2.1
  let f : ℕ → ℝ≥0∞ := fun n => if ω n = j then 1 else 0
  have hsum (r : ℕ) :
      (∑' n : ℕ, if (n : WithTop ℕ) < returnTime i ω ∧ ω (n + r) = j
        then (1 : ℝ≥0∞) else 0) = ∑ n ∈ Finset.range m, f (n + r) := by
    rw [tsum_eq_sum (s := Finset.range m)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hlt : (n : WithTop ℕ) < returnTime i ω := by
        rw [hm]
        exact WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hn)
      simp [hlt, f]
    · intro n hn
      have hn : m ≤ n := not_lt.mp (fun h => hn (Finset.mem_range.mpr h))
      have hle : returnTime i ω ≤ (n : WithTop ℕ) := by rw [hm]; exact WithTop.coe_le_coe.mpr hn
      simp [not_lt.mpr hle]
  have hf : f m = f 0 := by simp [f, hmi, h0]
  have hfin : f 0 ≠ ⊤ := by simp [f]; split_ifs <;> simp
  have he : (∑ n ∈ Finset.range m, f (n + 1)) + f 0 =
      (∑ n ∈ Finset.range m, f n) + f 0 := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ, hf]
  rw [hsum 1]
  change _ = ∑' n : ℕ, if (n : WithTop ℕ) < returnTime i ω ∧ ω n = j then 1 else 0
  have hz := hsum 0
  simp only [Nat.add_zero] at hz
  rw [hz]
  exact (ENNReal.add_left_inj hfin).mp he

/-- The excursion measure is invariant even when its total mass is infinite. -/
theorem excursionMass_invariant (P : StochasticMatrix S) (i : S)
    (hi : Recurrent P i) (j : S) :
    ∑' k, excursionMass P i k * P k j = excursionMass P i j := by
  classical
  have hm (n : ℕ) : MeasurableSet {ω : ℕ → S |
      (n : WithTop ℕ) < returnTime i ω ∧ ω (n + 1) = j} :=
    (coordinateFiltration.le n _ (measurableSet_excursionAlive i n)).inter
      (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
  have hrec : ∀ᵐ ω ∂statePathLaw P i, returnTime i ω < ⊤ :=
    (mem_ae_iff_prob_eq_one (measurableSet_returnTime_finite i)).mpr hi
  calc
    (∑' k, excursionMass P i k * P k j) =
        ∑' k, ∑' n : ℕ, statePathLaw P i
          {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω n = k} * P k j := by
      simp_rw [excursionMass_eq_tsum, ENNReal.tsum_mul_right]
    _ = ∑' n : ℕ, ∑' k, statePathLaw P i
          {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω n = k} * P k j := ENNReal.tsum_comm
    _ = ∑' n : ℕ, statePathLaw P i
          {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω (n + 1) = j} := by
      apply tsum_congr
      intro n
      exact excursion_transition P i j n
    _ = ∫⁻ ω, ∑' n : ℕ,
          if (n : WithTop ℕ) < returnTime i ω ∧ ω (n + 1) = j
          then (1 : ℝ≥0∞) else 0 ∂statePathLaw P i := by
      rw [lintegral_tsum (fun n =>
        (Measurable.ite (hm n) measurable_const measurable_const).aemeasurable)]
      apply tsum_congr
      intro n
      simpa [Set.indicator_apply] using
        (lintegral_indicator (μ := statePathLaw P i) (f := fun _ => (1 : ℝ≥0∞)) (hm n)).symm
    _ = excursionMass P i j := by
      apply lintegral_congr_ae
      filter_upwards [hrec, statePathLaw_initial P i] with ω ht h0
      exact excursionVisits_shift i j ω h0 ht

/-- Invariance iterates by nonnegative summation, without any finite-mass hypothesis. -/
theorem excursionMass_invariant_power (P : StochasticMatrix S) (i : S)
    (hi : Recurrent P i) (n : ℕ) (j : S) :
    ∑' k, excursionMass P i k * power P n k j = excursionMass P i j := by
  induction n generalizing j with
  | zero => simp [power_zero, identity_apply]
  | succ n ih =>
    calc
      (∑' k, excursionMass P i k * power P (n + 1) k j) =
          ∑' k, ∑' l, (excursionMass P i k * power P n k l) * P l j := by
        simp_rw [power_succ, comp_apply, ← ENNReal.tsum_mul_left, mul_assoc]
      _ = ∑' l, ∑' k, (excursionMass P i k * power P n k l) * P l j :=
        ENNReal.tsum_comm
      _ = ∑' l, excursionMass P i l * P l j := by
        simp_rw [ENNReal.tsum_mul_right, ih]
      _ = excursionMass P i j := excursionMass_invariant P i hi j

/-- A positive route back to the reference state bounds each coordinate. -/
theorem excursionMass_finite (P : StochasticMatrix S) (hP : Irreducible P)
    (i : S) (hi : Recurrent P i) (j : S) : excursionMass P i j < ⊤ := by
  obtain ⟨n, hn⟩ := (hP j i).1
  have hb : excursionMass P i j * power P n j i ≤ 1 := by
    calc
      excursionMass P i j * power P n j i ≤
          ∑' k, excursionMass P i k * power P n k i :=
            ENNReal.le_tsum (f := fun k => excursionMass P i k * power P n k i) j
      _ = 1 := (excursionMass_invariant_power P i hi n i).trans (excursionMass_self P i)
  exact ENNReal.lt_top_of_mul_ne_top_left (lt_of_le_of_lt hb ENNReal.one_lt_top).ne hn.ne'

/-- The total mass is nonzero since the reference coordinate has mass one. -/
theorem one_le_meanReturnTime (P : StochasticMatrix S) (i : S) :
    1 ≤ meanReturnTime P i := by
  rw [← excursionMass_total, ← excursionMass_self P i]
  exact ENNReal.le_tsum i

theorem normalizedExcursion_stationary (P : StochasticMatrix S) (i : S)
    (hi : PositiveRecurrent P i) :
    (∑' j, normalizedExcursionMass P i j = 1) ∧
      ∀ j, ∑' k, normalizedExcursionMass P i k * P k j = normalizedExcursionMass P i j := by
  have hne : meanReturnTime P i ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_meanReturnTime P i))
  have hr := positiveRecurrent_recurrent P i hi
  constructor
  · simp only [normalizedExcursionMass, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, excursionMass_total, ENNReal.mul_inv_cancel hne hi.ne]
  · intro j
    simp only [normalizedExcursionMass, div_eq_mul_inv]
    simp_rw [mul_right_comm (excursionMass P i _) (meanReturnTime P i)⁻¹]
    rw [ENNReal.tsum_mul_right, excursionMass_invariant P i hr]

theorem excursion_stationary_probability (P : StochasticMatrix S) (i : S)
    (hi : PositiveRecurrent P i) :
    ∃ ν : ProbabilityLaw S, (∀ j, ν j = excursionMass P i j / meanReturnTime P i) ∧
      ν.bind P = ν := by
  obtain ⟨hsum, hinv⟩ := normalizedExcursion_stationary P i hi
  let ν : ProbabilityLaw S :=
    ⟨normalizedExcursionMass P i, ENNReal.summable.hasSum_iff.mpr hsum⟩
  refine ⟨ν, fun _ => rfl, ?_⟩
  apply PMF.ext
  intro j
  change (ν.bind P) j = normalizedExcursionMass P i j
  rw [PMF.bind_apply]
  exact hinv j

end
end P207.Markov
