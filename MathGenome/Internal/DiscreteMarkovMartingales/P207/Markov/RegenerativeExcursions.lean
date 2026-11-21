import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RegenerativeExcursions
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.StationaryReturnTimes
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.ClosedRecurrentClasses
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.StrongMarkov

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal MeasureTheory Classical
universe u v
namespace P207.Markov
noncomputable section

private theorem untopA_coe_nat (n : ℕ) : (n : WithTop ℕ).untopA = n := rfl
attribute [local simp] untopA_coe_nat

namespace RegenerativeExcursions
abbrev returnEpoch : RegenerativeExcursionsSpec.returnEpochType.{u,v} := @P207.Markov.returnEpoch
abbrev excursionVector : RegenerativeExcursionsSpec.excursionVectorType.{u,v} := @P207.Markov.excursionVector
abbrev singleExcursionVector : RegenerativeExcursionsSpec.singleExcursionVectorType.{u} := @P207.Markov.singleExcursionVector
end RegenerativeExcursions

/-- Infinity is absorbing; an undefined cycle cannot restart at time zero. -/
theorem returnEpoch_succ_of_top {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (i : S) (s : ℕ) (ω : Ω) (h : returnEpoch X i s ω = ⊤) :
    returnEpoch X i (s + 1) ω = ⊤ := by
  simp [returnEpoch, h]

theorem returnEpoch_succ_of_finite {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (i : S) (s n : ℕ) (ω : Ω) (h : returnEpoch X i s ω = n) :
    returnEpoch X i (s + 1) ω = hittingAfter X {i} (n + 1) ω := by
  simp only [returnEpoch, h]
  rfl

/-- The exact finite-layer decomposition needed for stopping-time induction. -/
theorem returnEpoch_succ_le_iff {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (i : S) (s n : ℕ) (ω : Ω) :
    returnEpoch X i (s + 1) ω ≤ n ↔
      ∃ a : ℕ, a < n ∧ returnEpoch X i s ω = a ∧
        hittingAfter X {i} (a + 1) ω ≤ n := by
  cases ht : returnEpoch X i s ω with
  | top => simp [returnEpoch_succ_of_top X i s ω ht]
  | coe a =>
    rw [returnEpoch_succ_of_finite X i s a ω ht]
    constructor
    · intro hn
      have ha := (le_hittingAfter (u := X) (s := {i}) (n := a + 1) ω).trans hn
      exact ⟨a, by exact Nat.lt_of_succ_le (WithTop.coe_le_coe.mp ha), rfl, hn⟩
    · rintro ⟨b, _, hb, hn⟩
      have hab : a = b := WithTop.coe_injective hb
      simpa only [hab] using hn

theorem returnEpoch_isStoppingTime :
    RegenerativeExcursionsSpec.returnEpoch_isStoppingTime.{u,v} := by
  intro S _ _ Ω m X ℱ hX i s
  induction s with
  | zero => exact hX.isStoppingTime_hittingAfter (measurableSet_singleton i)
  | succ s ih =>
    intro n
    have he : {ω | returnEpoch X i (s + 1) ω ≤ n} =
        ⋃ a : ℕ, ⋃ (_ : a < n),
          {ω | returnEpoch X i s ω = a} ∩ {ω | hittingAfter X {i} (a + 1) ω ≤ n} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
        returnEpoch_succ_le_iff]
      aesop
    rw [he]
    exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun han =>
      (ℱ.mono han.le _ (P207.stopping_layer_measurable ih a)).inter
        ((hX.isStoppingTime_hittingAfter (n := a + 1) (measurableSet_singleton i)) n)


/-- Return epochs are ordinary measurable random variables as well as stopping times. -/
theorem measurable_returnEpoch {S : Type u} [MeasurableSpace S]
    [MeasurableSingletonClass S] {Ω : Type v} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (hX : Adapted ℱ X) (i : S) (s : ℕ) :
    Measurable (returnEpoch X i s) :=
  MeasureTheory.IsStoppingTime.measurable' (returnEpoch_isStoppingTime X ℱ hX i s)

/-- Measurability of a finite interval reward with random countable endpoints. -/
theorem measurable_intervalReward {Ω : Type v} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k))
    (a b : Ω → ℕ) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => ∑ k ∈ Finset.Ico (a ω) (b ω), Y k ω) := by
  have hF : Measurable (fun z : (ℕ × ℕ) × Ω =>
      ∑ k ∈ Finset.Ico z.1.1 z.1.2, Y k z.2) := by
    apply measurable_from_prod_countable_right
    intro ab
    exact (Finset.Ico ab.1 ab.2).measurable_sum (fun k _ => hY k)
  exact hF.comp ((ha.prodMk hb).prodMk measurable_id)

theorem measurable_excursionVector :
    RegenerativeExcursionsSpec.measurable_excursionVector.{u,v} := by
  intro S _ _ _ Ω m X ℱ hX i f s
  have ha := measurable_returnEpoch X ℱ hX i s
  have hb := measurable_returnEpoch X ℱ hX i (s + 1)
  have hau : Measurable (fun ω => (returnEpoch X i s ω).untopA) :=
    (measurable_of_countable _).comp ha
  have hbu : Measurable (fun ω => (returnEpoch X i (s + 1) ω).untopA) :=
    (measurable_of_countable _).comp hb
  have hsum := measurable_intervalReward (fun k ω => f (X k ω))
    (fun k => (measurable_of_countable f).comp hX.measurable) _ _ hau hbu
  have habs := measurable_intervalReward (fun k ω => |f (X k ω)|)
    (fun k => (measurable_of_countable (fun j => |f j|)).comp hX.measurable) _ _ hau hbu
  have hlen : Measurable (fun ω =>
      (((returnEpoch X i (s + 1) ω).untopA - (returnEpoch X i s ω).untopA : ℕ) : ℝ)) :=
    (measurable_of_countable (fun ab : ℕ × ℕ => ((ab.1 - ab.2 : ℕ) : ℝ))).comp
      (hbu.prodMk hau)
  exact measurable_const.ite
    ((measurableSet_eq_fun ha measurable_const).union
      (measurableSet_eq_fun hb measurable_const)) (hlen.prodMk (hsum.prodMk habs))

theorem measurable_singleExcursionVector :
    RegenerativeExcursionsSpec.measurable_singleExcursionVector.{u} := by
  intro S _ _ _ i f
  have ht := measurable_returnTime i
  have hu : Measurable (fun p : ℕ → S => (returnTime i p).untopA) :=
    (measurable_of_countable _).comp ht
  have hsum : Measurable (fun p : ℕ → S =>
      ∑ k ∈ Finset.range (returnTime i p).untopA, f (p k)) := by
    simpa only [Nat.Ico_zero_eq_range] using
      measurable_intervalReward (fun k (p : ℕ → S) => f (p k))
        (fun k => (measurable_of_countable f).comp (measurable_pi_apply k))
        (fun _ => 0) _ measurable_const hu
  have habs : Measurable (fun p : ℕ → S =>
      ∑ k ∈ Finset.range (returnTime i p).untopA, |f (p k)|) := by
    simpa only [Nat.Ico_zero_eq_range] using
      measurable_intervalReward (fun k (p : ℕ → S) => |f (p k)|)
        (fun k => (measurable_of_countable (fun j => |f j|)).comp (measurable_pi_apply k))
        (fun _ => 0) _ measurable_const hu
  have hlen : Measurable (fun p : ℕ → S => ((returnTime i p).untopA : ℝ)) :=
    (measurable_of_countable _).comp hu
  exact measurable_const.ite (measurableSet_eq_fun ht measurable_const)
    (hlen.prodMk (hsum.prodMk habs))


/-- Every return epoch exists on a path with arbitrarily late visits. -/
theorem returnEpoch_finite_of_unbounded {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (ω : Ω)
    (h : ∀ n : ℕ, ∃ k, n ≤ k ∧ X k ω = i) :
    ∀ s, returnEpoch X i s ω < ⊤ := by
  have hh (n : ℕ) : hittingAfter X {i} n ω < ⊤ := by
    obtain ⟨k, hk, hki⟩ := h n
    exact lt_of_le_of_lt (hittingAfter_le_of_mem hk hki) (WithTop.coe_lt_top k)
  intro s
  induction s with
  | zero => exact hh 0
  | succ s ih =>
    cases ht : returnEpoch X i s ω with
    | top => simp only [ht, lt_self_iff_false] at ih
    | coe n => rw [returnEpoch_succ_of_finite X i s n ω ht]; exact hh (n + 1)

/-- The fixed-time future law and recurrent hitting give arbitrarily late
visits for an arbitrary initial law, without a stationarity assumption on X. -/
theorem chain_unbounded_visits {S : Type u} [Countable S] [Nonempty S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hc : IsMarkovChain P ν X ℱ μ) (i : S)
    (hhit : ∀ j, hittingProbability P {i} j = 1) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, ∃ k, n ≤ k ∧ X k ω = i := by
  let B : Set (ℕ → S) := {p | hittingTime {i} p < ⊤}
  have hB : MeasurableSet B := measurableSet_hittingTime_finite {i}
  have hfuture (n : ℕ) : Measurable (fun ω k => X (n + k) ω) :=
    measurable_pi_iff.mpr fun _ => hc.1.measurable
  have he (n : ℕ) : μ {ω | (fun k => X (n + k) ω) ∈ B} = 1 := by
    have h := StrongMarkov.fixed_future_lintegral hc
      (B.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hB)
      n Set.univ MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    have hr (j : S) : (∫⁻ p, B.indicator (fun _ => (1 : ℝ≥0∞)) p
        ∂statePathLaw P j) = 1 := by
      simpa only [lintegral_indicator hB, lintegral_const, one_mul,
        Measure.restrict_apply_univ, hittingProbability, B] using hhit j
    simp_rw [hr] at h
    have hl : (fun ω => B.indicator (fun _ => (1 : ℝ≥0∞))
        (fun k => X (n + k) ω)) =
        {ω | (fun k => X (n + k) ω) ∈ B}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hl] at h
    have hC : MeasurableSet {ω | (fun k => X (n + k) ω) ∈ B} :=
      hB.preimage (hfuture n)
    have hiC := lintegral_indicator_const (μ := μ) hC (1 : ℝ≥0∞)
    simp only [one_mul] at hiC
    exact hiC.symm.trans (h.trans (by simp))
  have hae (n : ℕ) : ∀ᵐ ω ∂μ, (fun k => X (n + k) ω) ∈ B :=
    (mem_ae_iff_prob_eq_one (hB.preimage (hfuture n))).mpr (he n)
  filter_upwards [ae_all_iff.mpr hae] with ω hω n
  obtain ⟨k, hk⟩ := (hittingTime_finite_iff {i} _).mp (hω n)
  exact ⟨n + k, Nat.le_add_right _ _, hk⟩

theorem returnEpoch_finite : RegenerativeExcursionsSpec.returnEpoch_finite.{u,v} := by
  intro S _ _ _ _ Ω m P π ν X ℱ μ _ hP hπ hc i
  have hi : Recurrent P i :=
    positiveRecurrent_recurrent P i (stationary_positiveRecurrent P π hP hπ i)
  have hh := chain_unbounded_visits P ν X ℱ μ hc i
    (fun j => hittingProbability_recurrent_of_accessible P hi (hP i j).1)
  filter_upwards [hh] with ω hω
  exact returnEpoch_finite_of_unbounded X i ω hω


/-- A finite epoch is an actual visit to the reference state. -/
theorem returnEpoch_mem {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (i : S) (s : ℕ) (ω : Ω) (h : returnEpoch X i s ω < ⊤) :
    X (returnEpoch X i s ω).untopA ω = i := by
  cases s with
  | zero => exact hittingAfter_mem_set_of_ne_top h.ne
  | succ s =>
    cases ht : returnEpoch X i s ω with
    | top => simp [returnEpoch_succ_of_top X i s ω ht] at h
    | coe n =>
      have he := returnEpoch_succ_of_finite X i s n ω ht
      rw [he] at h ⊢
      exact hittingAfter_mem_set_of_ne_top h.ne

/-- Complete return epochs strictly increase, including on the way to infinity. -/
theorem returnEpoch_lt_succ {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (i : S) (s : ℕ) (ω : Ω) (h : returnEpoch X i s ω < ⊤) :
    returnEpoch X i s ω < returnEpoch X i (s + 1) ω := by
  cases ht : returnEpoch X i s ω with
  | top => simp [ht] at h
  | coe n =>
    rw [returnEpoch_succ_of_finite X i s n ω ht]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n))
      (le_hittingAfter ω)

theorem returnEpoch_mono {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (i : S) (ω : Ω) : Monotone (fun s => returnEpoch X i s ω) := by
  apply monotone_nat_of_le_succ
  intro s
  by_cases ht : returnEpoch X i s ω = ⊤
  · simp [ht, returnEpoch_succ_of_top X i s ω ht]
  · exact (returnEpoch_lt_succ X i s ω (lt_top_iff_ne_top.mpr ht)).le

/-- The absolute reward controls the signed reward pathwise, including all
undefined layers, where both sides are zero. -/
theorem excursionVector_abs_reward_le {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (f : S → ℝ) (s : ℕ) (ω : Ω) :
    |(excursionVector X i f s ω).2.1| ≤ (excursionVector X i f s ω).2.2 := by
  unfold excursionVector
  split_ifs
  · simp
  · dsimp only
    exact Finset.abs_sum_le_sum_abs (fun k => f (X k ω)) _

/-- Nonnegative reward accumulated before the first positive return. This
extended sum also records the no-return layer without an arbitrary truncation. -/
def excursionNonnegReward {S : Type u} (i : S) (g : S → ℝ≥0∞)
    (p : ℕ → S) : ℝ≥0∞ :=
  ∑' n : ℕ, if (n : WithTop ℕ) < returnTime i p then g (p n) else 0

/-- Partition a nonnegative excursion reward by the visited state. -/
theorem excursionNonnegReward_eq_visits {S : Type u} (i : S)
    (g : S → ℝ≥0∞) (p : ℕ → S) :
    excursionNonnegReward i g p = ∑' j, excursionVisits i j p * g j := by
  simp only [excursionNonnegReward, excursionVisits, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro n
  by_cases hn : (n : WithTop ℕ) < returnTime i p
  · simp [hn, eq_comm]
  · simp [hn]

/-- Tonelli turns arbitrary nonnegative rewards into the excursion occupation
masses already derived from the chain. -/
theorem lintegral_excursionNonnegReward {S : Type u} [Countable S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S) (g : S → ℝ≥0∞) :
    (∫⁻ p, excursionNonnegReward i g p ∂statePathLaw P i) =
      ∑' j, excursionMass P i j * g j := by
  simp_rw [excursionNonnegReward_eq_visits]
  rw [lintegral_tsum (fun j => ((measurable_excursionVisits i j).mul_const (g j)).aemeasurable)]
  apply tsum_congr
  intro j
  exact lintegral_mul_const _ (measurable_excursionVisits i j)

/-- On the finite return layer, the extended reward is the ordinary finite sum. -/
theorem excursionNonnegReward_of_finite {S : Type u} (i : S)
    (g : S → ℝ≥0∞) (p : ℕ → S) (b : ℕ) (hb : returnTime i p = b) :
    excursionNonnegReward i g p = ∑ n ∈ Finset.range b, g (p n) := by
  unfold excursionNonnegReward
  rw [tsum_eq_sum (s := Finset.range b)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [ite_eq_left (by rw [hb]; exact WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hn))]
  · intro n hn
    simp only [Finset.mem_range] at hn
    rw [ite_eq_right (by rw [hb]; exact fun h => hn (WithTop.coe_lt_coe.mp h))]

/-- Nonnegative rewards of a complete canonical excursion are nonnegative,
including the prescribed zero on the undefined layer. -/
theorem singleExcursionVector_reward_nonneg {S : Type u} (i : S) (g : S → ℝ)
    (hg : ∀ j, 0 ≤ g j) (p : ℕ → S) :
    0 ≤ (singleExcursionVector i g p).2.1 := by
  unfold singleExcursionVector
  split_ifs
  · exact le_rfl
  · dsimp only; exact Finset.sum_nonneg fun n _ => hg (p n)

/-- The ordinary reward agrees with its extended nonnegative version whenever
there is a return. -/
theorem ofReal_singleExcursionVector_reward {S : Type u} (i : S) (g : S → ℝ)
    (hg : ∀ j, 0 ≤ g j) (p : ℕ → S) (ht : returnTime i p < ⊤) :
    ENNReal.ofReal (singleExcursionVector i g p).2.1 =
      excursionNonnegReward i (fun j => ENNReal.ofReal (g j)) p := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp ht.ne
  rw [excursionNonnegReward_of_finite i _ p b hb.symm]
  simp only [singleExcursionVector, hb.symm, WithTop.coe_ne_top, ↓reduceIte,
    WithTop.untopA]
  exact ENNReal.ofReal_sum_of_nonneg (fun n _ => hg (p n))

/-- An ordinary nonnegative canonical reward is integrable exactly when its
occupation sum is finite; under stationarity this is the π-weighted sum. -/
theorem singleExcursionVector_nonneg_moment {S : Type u} [Countable S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hP : Irreducible P) (hπ : IsStationary P π) (i : S)
    (g : S → ℝ) (hg : ∀ j, 0 ≤ g j)
    (hs : Summable (fun j => (π j).toReal * g j)) :
    Integrable (fun p => (singleExcursionVector i g p).2.1) (statePathLaw P i) ∧
    (∫ p, (singleExcursionVector i g p).2.1 ∂statePathLaw P i) =
      ∑' j, ((π j).toReal / (π i).toReal) * g j := by
  let : Nonempty S := ⟨i⟩
  let : IsProbabilityMeasure (statePathLaw P i) := by unfold statePathLaw; infer_instance
  have hrec := positiveRecurrent_recurrent P i (stationary_positiveRecurrent P π hP hπ i)
  have ht : ∀ᵐ p ∂statePathLaw P i, returnTime i p < ⊤ :=
    (mem_ae_iff_prob_eq_one (measurableSet_returnTime_finite i)).mpr hrec
  have hm := (measurable_singleExcursionVector i g).snd.fst
  have hn : 0 ≤ᵐ[statePathLaw P i] (fun p => (singleExcursionVector i g p).2.1) :=
    ae_of_all _ (singleExcursionVector_reward_nonneg i g hg)
  have hs' : Summable (fun j => ((π j).toReal / (π i).toReal) * g j) := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs.mul_left ((π i).toReal)⁻¹
  have he (j : S) : excursionMass P i j * ENNReal.ofReal (g j) =
      ENNReal.ofReal (((π j).toReal / (π i).toReal) * g j) := by
    rw [stationary_excursionMass P π hP hπ i]
    rw [ENNReal.ofReal_mul (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      ← ENNReal.toReal_div, ENNReal.ofReal_toReal]
    exact ENNReal.div_ne_top (π.apply_ne_top j) (stationary_positive P π hP hπ i).ne'
  have hl : (∫⁻ p, ENNReal.ofReal (singleExcursionVector i g p).2.1 ∂statePathLaw P i) =
      ENNReal.ofReal (∑' j, ((π j).toReal / (π i).toReal) * g j) := by
    calc
      _ = ∫⁻ p, excursionNonnegReward i (fun j => ENNReal.ofReal (g j)) p
          ∂statePathLaw P i := by
        apply lintegral_congr_ae
        filter_upwards [ht] with p hp
        exact ofReal_singleExcursionVector_reward i g hg p hp
      _ = _ := by
        rw [lintegral_excursionNonnegReward]
        simp_rw [he]
        exact (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (hg j)) hs').symm
  constructor
  · exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hn).mp
      (by rw [hl]; exact ENNReal.ofReal_ne_top)
  · rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable, hl,
      ENNReal.toReal_ofReal (tsum_nonneg (fun j =>
        mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (hg j)))]

/-- Signed canonical rewards are integrable by the absolute reward assumption;
linearity is used only after proving integrability of nonnegative rewards. -/
theorem singleExcursionVector_signed_moment {S : Type u} [Countable S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hP : Irreducible P) (hπ : IsStationary P π) (i : S)
    (f : S → ℝ) (hf : Summable (fun j => (π j).toReal * |f j|)) :
    Integrable (fun p => (singleExcursionVector i f p).2.1) (statePathLaw P i) ∧
    (∫ p, (singleExcursionVector i f p).2.1 ∂statePathLaw P i) =
      ∑' j, ((π j).toReal / (π i).toReal) * f j := by
  have hsf : Summable (fun j => (π j).toReal * f j) :=
    hf.of_norm_bounded (fun j => by simp [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg])
  have hsg : Summable (fun j => (π j).toReal * (f j + |f j|)) := by
    simpa only [mul_add] using hsf.add hf
  obtain ⟨ha, hea⟩ := singleExcursionVector_nonneg_moment P π hP hπ i
    (fun j => |f j|) (fun j => abs_nonneg _) hf
  obtain ⟨hg, heg⟩ := singleExcursionVector_nonneg_moment P π hP hπ i
    (fun j => f j + |f j|) (fun j => by linarith [neg_abs_le (f j)]) hsg
  have he (p : ℕ → S) : (singleExcursionVector i f p).2.1 =
      (singleExcursionVector i (fun j => f j + |f j|) p).2.1 -
      (singleExcursionVector i (fun j => |f j|) p).2.1 := by
    unfold singleExcursionVector
    split_ifs
    · simp
    · dsimp only; rw [Finset.sum_add_distrib]; ring
  have hsa' : Summable (fun j => ((π j).toReal / (π i).toReal) * |f j|) := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hf.mul_left ((π i).toReal)⁻¹
  have hsg' : Summable (fun j => ((π j).toReal / (π i).toReal) * (f j + |f j|)) := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsg.mul_left ((π i).toReal)⁻¹
  constructor
  · exact (hg.sub ha).congr (ae_of_all _ (fun p => (he p).symm))
  · simp_rw [he]
    rw [integral_sub hg ha, heg, hea, ← hsg'.tsum_sub hsa']
    apply tsum_congr
    intro j
    ring

/-- All canonical moment formulas required for the regenerative theorem. -/
theorem singleExcursionVector_moments {S : Type u} [Countable S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hP : Irreducible P) (hπ : IsStationary P π) (i : S)
    (f : S → ℝ) (hf : Summable (fun j => (π j).toReal * |f j|)) :
    Integrable (fun p => (singleExcursionVector i f p).1) (statePathLaw P i) ∧
    Integrable (fun p => (singleExcursionVector i f p).2.1) (statePathLaw P i) ∧
    Integrable (fun p => (singleExcursionVector i f p).2.2) (statePathLaw P i) ∧
    (∫ p, (singleExcursionVector i f p).1 ∂statePathLaw P i) = 1 / (π i).toReal ∧
    (∫ p, (singleExcursionVector i f p).2.1 ∂statePathLaw P i) =
      ∑' j, ((π j).toReal / (π i).toReal) * f j ∧
    (∫ p, (singleExcursionVector i f p).2.2 ∂statePathLaw P i) =
      ∑' j, ((π j).toReal / (π i).toReal) * |f j| := by
  have hsum : Summable (fun j => (π j).toReal * (1 : ℝ)) := by
    simpa only [mul_one] using ENNReal.summable_toReal (show ∑' j, π j ≠ ⊤ by rw [π.tsum_coe]; simp)
  obtain ⟨hl, hel⟩ := singleExcursionVector_nonneg_moment P π hP hπ i
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one) hsum
  obtain ⟨hb, heb⟩ := singleExcursionVector_signed_moment P π hP hπ i f hf
  obtain ⟨hc, hec⟩ := singleExcursionVector_nonneg_moment P π hP hπ i
    (fun j => |f j|) (fun _ => abs_nonneg _) hf
  have heL (p : ℕ → S) : (singleExcursionVector i f p).1 =
      (singleExcursionVector i (fun _ => (1 : ℝ)) p).2.1 := by
    unfold singleExcursionVector
    split_ifs <;> simp
  have heC (p : ℕ → S) : (singleExcursionVector i f p).2.2 =
      (singleExcursionVector i (fun j => |f j|) p).2.1 := by
    simp only [singleExcursionVector]; split_ifs <;> rfl
  refine ⟨?_, hb, ?_, ?_, heb, ?_⟩
  · simpa only [heL] using hl
  · simpa only [heC] using hc
  · simp_rw [heL]
    rw [hel]
    simp only [mul_one, div_eq_mul_inv, tsum_mul_right]
    rw [← ENNReal.tsum_toReal_eq (fun j => π.apply_ne_top j), π.tsum_coe]
    simp
  · simpa only [heC] using hec

/-- The first positive return on a shifted finite cycle is its length. -/
theorem returnTime_shift_of_returnEpochs {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (s a b : ℕ) (ω : Ω)
    (ha : returnEpoch X i s ω = a) (hb : returnEpoch X i (s + 1) ω = b) :
    returnTime i (fun k => X (a + k) ω) = (b - a : ℕ) := by
  have hab : a < b := by
    have h := returnEpoch_lt_succ X i s ω (ha ▸ WithTop.coe_lt_top a)
    rw [ha, hb] at h
    exact WithTop.coe_lt_coe.mp h
  have hhit : hittingAfter X {i} (a + 1) ω = b :=
    (returnEpoch_succ_of_finite X i s a ω ha).symm.trans hb
  have hbi : X b ω = i := by
    have h := returnEpoch_mem X i (s + 1) ω (hb ▸ WithTop.coe_lt_top b)
    simpa only [hb, untopA_coe_nat] using h
  have hu : returnTime i (fun k => X (a + k) ω) ≤ (b - a : ℕ) := by
    apply (positiveReturnTime_le_iff coordinate i _ _).mpr
    exact ⟨b - a, by omega, le_rfl, by simpa only [coordinate, Nat.add_sub_of_le hab.le] using hbi⟩
  apply le_antisymm hu
  cases ht : returnTime i (fun k => X (a + k) ω) with
  | top => exact le_top
  | coe c =>
    obtain ⟨k, hk, hkc, hki⟩ := (positiveReturnTime_le_iff coordinate i _ c).mp ht.le
    have hle : (b : WithTop ℕ) ≤ (a + k : ℕ) := by
      rw [← hhit]
      exact hittingAfter_le_of_mem (u := X) (s := {i}) (n := a + 1)
        (i := a + k) (ω := ω) (by omega) hki
    have hbka : b ≤ a + k := WithTop.coe_le_coe.mp hle
    exact WithTop.coe_le_coe.mpr (show b - a ≤ c by omega)

/-- The actual excursion vector is the canonical excursion functional of the
future at its starting epoch on every complete finite cycle. -/
theorem excursionVector_eq_single_shiftedPath {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (f : S → ℝ) (s : ℕ) (ω : Ω)
    (ha : returnEpoch X i s ω < ⊤) (hb : returnEpoch X i (s + 1) ω < ⊤) :
    excursionVector X i f s ω =
      singleExcursionVector i f (shiftedPath X (returnEpoch X i s) (fun _ => i) ω) := by
  obtain ⟨a, ha'⟩ := WithTop.ne_top_iff_exists.mp ha.ne
  obtain ⟨b, hb'⟩ := WithTop.ne_top_iff_exists.mp hb.ne
  have ht := returnTime_shift_of_returnEpochs X i s a b ω ha'.symm hb'.symm
  have hshift : shiftedPath X (returnEpoch X i s) (fun _ => i) ω =
      fun k => X (a + k) ω := by
    simp only [shiftedPath, ha'.symm, WithTop.coe_ne_top, ↓reduceIte]; rfl
  rw [hshift]
  simp only [excursionVector, ha'.symm, hb'.symm, singleExcursionVector, ht]
  simp only [show ((b - a : ℕ) : WithTop ℕ) ≠ ⊤ from WithTop.coe_ne_top,
    ↓reduceIte, untopA_coe_nat]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact Finset.sum_Ico_eq_sum_range (fun k => f (X k ω)) a b
    · exact Finset.sum_Ico_eq_sum_range (fun k => |f (X k ω)|) a b

/-- Every completed vector is measurable in the past at its ending epoch.
On a finite ending layer it is a function of a finite prefix. -/
theorem measurable_excursionVector_stopped {S : Type u} [Countable S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (hX : Adapted ℱ X)
    (i : S) (f : S → ℝ) (s : ℕ) :
    Measurable[P207.stoppedSigma (returnEpoch_isStoppingTime X ℱ hX i (s + 1))]
      (excursionVector X i f s) := by
  let ℱ' : Filtration ℕ (P207.terminalSigma ℱ) :=
    ⟨ℱ, fun _ _ h => ℱ.mono h, fun n => le_iSup ℱ n⟩
  have hm : Measurable[P207.terminalSigma ℱ] (excursionVector X i f s) :=
    @measurable_excursionVector S _ _ _ Ω (P207.terminalSigma ℱ) X ℱ' hX i f s
  intro D hD
  apply (P207.stoppedSigma_layers (returnEpoch_isStoppingTime X ℱ hX i (s + 1)) _).mpr
  refine ⟨hD.preimage hm, fun n => ?_⟩
  let V : ℕ → Ω → ℝ × ℝ × ℝ := fun a ω =>
    (((n - a : ℕ) : ℝ), ∑ k ∈ Finset.Ico a n, f (X k ω),
      ∑ k ∈ Finset.Ico a n, |f (X k ω)|)
  have hV (a : ℕ) : Measurable[ℱ n] (V a) := by
    have hY (k : ℕ) (hk : k ∈ Finset.Ico a n) : Measurable[ℱ n] (X k) :=
      (hX k).mono (ℱ.mono (Finset.mem_Ico.mp hk).2.le) le_rfl
    exact measurable_const.prodMk
      (((Finset.Ico a n).measurable_sum (fun k hk => (measurable_of_countable f).comp (hY k hk))).prodMk
        ((Finset.Ico a n).measurable_sum (fun k hk =>
          (measurable_of_countable (fun j => |f j|)).comp (hY k hk))))
  have he : excursionVector X i f s ⁻¹' D ∩ {ω | returnEpoch X i (s + 1) ω = n} =
      ⋃ a : ℕ, ⋃ (_ : a < n), {ω | returnEpoch X i s ω = a} ∩
        {ω | returnEpoch X i (s + 1) ω = n} ∩ (V a ⁻¹' D) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hω, hn⟩
      obtain ⟨a, han, ha, _⟩ := (returnEpoch_succ_le_iff X i s n ω).mp hn.le
      refine ⟨a, han, ⟨ha, hn⟩, ?_⟩
      simpa [excursionVector, ha, hn, V] using hω
    · rintro ⟨a, _, ⟨ha, hn⟩, hω⟩
      refine ⟨?_, hn⟩
      simpa [excursionVector, ha, hn, V] using hω
  rw [he]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun han =>
    ((ℱ.mono han.le _ (P207.stopping_layer_measurable
      (returnEpoch_isStoppingTime X ℱ hX i s) a)).inter
      (P207.stopping_layer_measurable (returnEpoch_isStoppingTime X ℱ hX i (s + 1)) n)).inter
      (hD.preimage (hV a))

/-- Previous complete excursions are known at any later starting epoch. -/
theorem measurable_excursionVector_past {S : Type u} [Countable S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (hX : Adapted ℱ X)
    (i : S) (f : S → ℝ) {t s : ℕ} (hts : t < s) :
    Measurable[P207.stoppedSigma (returnEpoch_isStoppingTime X ℱ hX i s)]
      (excursionVector X i f t) :=
  (measurable_excursionVector_stopped X ℱ hX i f t).mono
    (P207.stoppedSigma_mono _ _ (fun ω => returnEpoch_mono X i ω (Nat.succ_le_iff.mpr hts))) le_rfl

/-- The stopped state at any return epoch is the reference state. The fallback
is chosen to be that same state on the infinite layer. -/
theorem stoppedState_returnEpoch {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (s : ℕ) (ω : Ω) :
    stoppedState X (returnEpoch X i s) i ω = i := by
  unfold stoppedState
  split_ifs with h
  · rfl
  · exact returnEpoch_mem X i s ω (lt_top_iff_ne_top.mpr h)

/-- Strong Markov gives a fixed excursion law independent of every event
in the stopped past. Finiteness is derived separately from recurrence. -/
theorem excursionVector_event_factor {S : Type u} [Countable S] [Nonempty S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hc : IsMarkovChain P ν X ℱ μ) (i : S) (f : S → ℝ)
    (hf : ∀ᵐ ω ∂μ, ∀ s, returnEpoch X i s ω < ⊤)
    (s : ℕ) (A : Set Ω)
    (hA : MeasurableSet[P207.stoppedSigma (returnEpoch_isStoppingTime X ℱ hc.1 i s)] A)
    (D : Set (ℝ × ℝ × ℝ)) (hD : MeasurableSet D) :
    μ (A ∩ (excursionVector X i f s ⁻¹' D)) =
      μ A * statePathLaw P i (singleExcursionVector i f ⁻¹' D) := by
  let B := singleExcursionVector i f ⁻¹' D
  have hB : MeasurableSet B := hD.preimage (measurable_singleExcursionVector i f)
  have hV : Measurable (excursionVector X i f s) := measurable_excursionVector X ℱ hc.1 i f s
  have hA' : MeasurableSet A := (P207.terminalSigma_le ℱ) _
    ((P207.stoppedSigma_le_terminal _) _ hA)
  have hrestr : μ.restrict (A ∩ {ω | returnEpoch X i s ω < ⊤}) = μ.restrict A := by
    apply Measure.restrict_congr_set
    filter_upwards [hf] with ω hω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hω s, and_true]
  have h := strong_future_lintegral P ν X ℱ μ hc (returnEpoch X i s)
    (returnEpoch_isStoppingTime X ℱ hc.1 i s) (fun _ => i) i
    (B.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hB) A hA
  rw [hrestr] at h
  simp_rw [stoppedState_returnEpoch] at h
  have hcan : (∫⁻ p, B.indicator (fun _ => (1 : ℝ≥0∞)) p ∂statePathLaw P i) =
      statePathLaw P i B := by
    simpa only [one_mul] using lintegral_indicator_const (μ := statePathLaw P i) hB (1 : ℝ≥0∞)
  rw [hcan, lintegral_const, Measure.restrict_apply_univ] at h
  have hl : (∫⁻ ω in A, B.indicator (fun _ => (1 : ℝ≥0∞))
      (shiftedPath X (returnEpoch X i s) (fun _ => i) ω) ∂μ) =
      μ (A ∩ (excursionVector X i f s ⁻¹' D)) := by
    calc
      _ = ∫⁻ ω in A, (excursionVector X i f s ⁻¹' D).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hf] with ω hω
        have he := excursionVector_eq_single_shiftedPath X i f s ω (hω s) (hω (s + 1))
        simp only [Set.indicator_apply, Set.mem_preimage, B, ← he]
      _ = _ := by
        rw [lintegral_indicator_const (hD.preimage hV), one_mul,
          Measure.restrict_apply (hD.preimage hV), Set.inter_comm]
  rw [hl] at h
  exact h.trans (mul_comm _ _)

/-- Each complete cycle has the law of a canonical excursion from `i`. -/
theorem excursionVector_identDistrib {S : Type u} [Countable S] [Nonempty S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hc : IsMarkovChain P ν X ℱ μ) (i : S) (f : S → ℝ)
    (hf : ∀ᵐ ω ∂μ, ∀ s, returnEpoch X i s ω < ⊤) (s : ℕ) :
    IdentDistrib (excursionVector X i f s) (singleExcursionVector i f)
      μ (statePathLaw P i) := by
  have hm := measurable_excursionVector X ℱ hc.1 i f s
  have hn := measurable_singleExcursionVector i f
  refine ⟨hm.aemeasurable, hn.aemeasurable, ?_⟩
  apply Measure.ext
  intro D hD
  rw [Measure.map_apply hm hD, Measure.map_apply hn hD]
  simpa only [Set.univ_inter, measure_univ, one_mul] using
    excursionVector_event_factor P ν X ℱ μ hc i f hf s Set.univ MeasurableSet.univ D hD

/-- Finite intersection induction, peeling off the largest index, upgrades
independence from the stopped past to independence of the entire sequence. -/
theorem excursionVector_iIndepFun {S : Type u} [Countable S] [Nonempty S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hc : IsMarkovChain P ν X ℱ μ) (i : S) (f : S → ℝ)
    (hf : ∀ᵐ ω ∂μ, ∀ s, returnEpoch X i s ω < ⊤) :
    iIndepFun (excursionVector X i f) μ := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro J D hD
  revert hD
  induction J using Finset.induction_on_max with
  | empty => intro _; simp
  | insert s J hJs ih =>
    intro hD
    have hs : s ∉ J := fun h => (lt_self_iff_false s).mp (hJs s h)
    have hDs := hD s (Finset.mem_insert_self s J)
    have hDJ : ∀ j ∈ J, MeasurableSet (D j) :=
      fun j hj => hD j (Finset.mem_insert_of_mem hj)
    let A := ⋂ j ∈ J, excursionVector X i f j ⁻¹' D j
    have hA : MeasurableSet[P207.stoppedSigma (returnEpoch_isStoppingTime X ℱ hc.1 i s)] A :=
      MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj =>
        (hDJ j hj).preimage (measurable_excursionVector_past X ℱ hc.1 i f (hJs j hj))
    have hfactor := excursionVector_event_factor P ν X ℱ μ hc i f hf s A hA (D s) hDs
    have hmarginal := excursionVector_event_factor P ν X ℱ μ hc i f hf s
      Set.univ MeasurableSet.univ (D s) hDs
    simp only [Set.univ_inter, measure_univ, one_mul] at hmarginal
    have he : (⋂ j ∈ insert s J, excursionVector X i f j ⁻¹' D j) =
        A ∩ (excursionVector X i f s ⁻¹' D s) := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_insert, Set.mem_inter_iff, A]
      aesop
    rw [he, hfactor, ← hmarginal, Finset.prod_insert hs]
    rw [show μ A = ∏ j ∈ J, μ (excursionVector X i f j ⁻¹' D j) from ih hDJ]
    exact mul_comm _ _

/-- Regeneration, independence and finite reward moments, all derived from the
Markov chain and its stationary excursion occupation measure. -/
theorem regenerative_excursions : RegenerativeExcursionsSpec.regenerative_excursions.{u,v} := by
  intro S _ _ _ _ Ω m P π ν X ℱ μ _ hP hπ hc i f hf
  have hfin := returnEpoch_finite P π ν X ℱ μ hP hπ hc i
  have hid := excursionVector_identDistrib P ν X ℱ μ hc i f hfin
  refine ⟨hfin, measurable_excursionVector X ℱ hc.1 i f,
    excursionVector_iIndepFun P ν X ℱ μ hc i f hfin, hid, fun s => ?_⟩
  obtain ⟨hL, hB, hC, heL, heB, heC⟩ := singleExcursionVector_moments P π hP hπ i f hf
  have hdl := (hid s).comp measurable_fst
  have hdb := (hid s).comp (measurable_fst.comp measurable_snd)
  have hdc := (hid s).comp (measurable_snd.comp measurable_snd)
  exact ⟨hdl.integrable_iff.mpr hL, hdb.integrable_iff.mpr hB,
    hdc.integrable_iff.mpr hC, hdl.integral_eq.trans heL,
    hdb.integral_eq.trans heB, hdc.integral_eq.trans heC⟩

end
end P207.Markov
