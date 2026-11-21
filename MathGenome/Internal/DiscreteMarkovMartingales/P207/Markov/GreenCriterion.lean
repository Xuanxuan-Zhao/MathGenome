import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.GreenCriterion
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.RecurrenceInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.StrongMarkov
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.DeterministicTransitions
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter
open scoped ENNReal MeasureTheory
set_option backward.isDefEq.respectTransparency false
universe u v
namespace P207.Markov
noncomputable section

namespace GreenCriterion
abbrev visitCount : GreenCriterionSpec.visitCountType := @P207.Markov.visitCount
abbrev greenSeries : GreenCriterionSpec.greenSeriesType := @P207.Markov.greenSeries
abbrev meanVisits : GreenCriterionSpec.meanVisitsType := @P207.Markov.meanVisits
end GreenCriterion

section Discrete
variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

local instance (P : StochasticMatrix S) (i : S) : IsProbabilityMeasure (statePathLaw P i) := by
  unfold statePathLaw
  infer_instance

theorem measurable_visitCount (i : S) : Measurable (visitCount i) := by
  apply Measurable.tsum
  intro n
  exact measurable_const.indicator (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)

/-- Tonelli applies to the nonnegative indicators, including an infinite count. -/
theorem greenSeries_eq_meanVisits (P : StochasticMatrix S) (i : S) :
    greenSeries P i = meanVisits P i := by
  letI : Nonempty S := ⟨i⟩
  unfold meanVisits visitCount greenSeries
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    rw [lintegral_indicator (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)]
    simp only [lintegral_one]
    have h := DeterministicTransitions.marginal_mass
      (coordinate_isMarkovChain P (PMF.pure i)) n i
    simpa [statePathLaw, coordinate, evolve, PMF.pure_bind] using h.symm
  · intro n
    exact (measurable_const.indicator
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)).aemeasurable

theorem visitCount_eq_encard {S : Type u} (i : S) (ω : ℕ → S) :
    visitCount i ω = ENat.toENNReal {n | ω n = i}.encard := by
  classical
  unfold visitCount
  have he : (fun n : ℕ => ({p : ℕ → S | p n = i}).indicator
      (fun _ => (1 : ℝ≥0∞)) ω) = ({n : ℕ | ω n = i}).indicator (fun _ => 1) := by
    funext n
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [he, ← tsum_subtype, ENNReal.tsum_set_one]

theorem visitCount_eq_top_iff (i : S) (ω : ℕ → S) :
    visitCount i ω = ⊤ ↔ Set.Infinite {n | ω n = i} := by
  rw [visitCount_eq_encard]
  simp

/-- A count, finite or infinite, is the sum of its positive integer tails. -/
theorem visitCount_eq_tsum_tails (i : S) (ω : ℕ → S) :
    visitCount i ω = ∑' k : ℕ,
      if (k + 1 : ℝ≥0∞) ≤ visitCount i ω then 1 else 0 := by
  classical
  rw [visitCount_eq_encard]
  generalize {n | ω n = i}.encard = a
  induction a using ENat.recTopCoe with
  | top => simp
  | coe a =>
    change (a : ℝ≥0∞) = ∑' k : ℕ, if (k + 1 : ℝ≥0∞) ≤ a then 1 else 0
    rw [tsum_eq_sum (s := Finset.range a)]
    · have he : (∑ k ∈ Finset.range a, if (k + 1 : ℝ≥0∞) ≤ a then (1 : ℝ≥0∞) else 0) =
          ∑ _k ∈ Finset.range a, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply ite_eq_left
        exact_mod_cast (Nat.add_one_le_iff.mpr (Finset.mem_range.mp hk))
      rw [he]
      simp
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      have h : ¬ (k + 1 : ℝ≥0∞) ≤ a := by exact_mod_cast (by omega : ¬ k + 1 ≤ a)
      simp [h]

theorem meanVisits_eq_tsum_tails (P : StochasticMatrix S) (i : S) :
    meanVisits P i = ∑' k : ℕ,
      statePathLaw P i {ω | (k + 1 : ℝ≥0∞) ≤ visitCount i ω} := by
  classical
  unfold meanVisits
  have he : (fun ω : ℕ → S => visitCount i ω) = (fun ω => ∑' k : ℕ,
      if (k + 1 : ℝ≥0∞) ≤ visitCount i ω then 1 else 0) :=
    funext (visitCount_eq_tsum_tails i)
  conv_lhs => rw [he]
  have hm (k : ℕ) : Measurable (fun ω : ℕ → S =>
      if (k + 1 : ℝ≥0∞) ≤ visitCount i ω then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (measurable_visitCount i))
      measurable_const measurable_const
  rw [lintegral_tsum (fun k => (hm k).aemeasurable)]
  apply tsum_congr
  intro k
  have he' : (fun ω : ℕ → S =>
      if (k + 1 : ℝ≥0∞) ≤ visitCount i ω then (1 : ℝ≥0∞) else 0) =
      ({ω | (k + 1 : ℝ≥0∞) ≤ visitCount i ω}).indicator (fun _ => 1) := by
    funext ω
    simp [Set.indicator_apply]
  rw [he', lintegral_indicator (measurableSet_le measurable_const (measurable_visitCount i))]
  simp

theorem chain_meanVisits [Nonempty S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (i : S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P (PMF.pure i) X ℱ μ) :
    (∫⁻ ω, visitCount i (fun n => X n ω) ∂μ) = meanVisits P i := by
  have hp : Measurable (fun ω n => X n ω) := Measurable.of_eval (fun n => h.1.measurable)
  rw [← lintegral_map (measurable_visitCount i) hp, chain_pathLaw P (PMF.pure i) X ℱ μ h]
  rfl

/-- A finite first positive return is a visit, preceded by no positive visit. -/
theorem returnTime_at_finite (i : S) (ω : ℕ → S) (n : ℕ)
    (hn : returnTime i ω = n) :
    1 ≤ n ∧ ω n = i ∧ ∀ k, 1 ≤ k → k < n → ω k ≠ i := by
  have hl : positiveReturnTime coordinate i ω ≤ n := hn.le
  obtain ⟨k, h1, h2, h3⟩ := (positiveReturnTime_le_iff coordinate i ω n).mp hl
  have hk : n ≤ k := WithTop.coe_le_coe.mp (hn.symm.le.trans
    ((positiveReturnTime_le_iff coordinate i ω k).mpr ⟨k, h1, le_rfl, h3⟩))
  have hkn : k = n := le_antisymm h2 hk
  subst k
  refine ⟨h1, h3, ?_⟩
  intro k hk hkn hki
  have ht := (positiveReturnTime_le_iff coordinate i ω k).mpr ⟨k, hk, le_rfl, hki⟩
  have hnk : n ≤ k := WithTop.coe_le_coe.mp (hn.symm.le.trans ht)
  omega

theorem visitCount_of_returnTime_top (i : S) (ω : ℕ → S) (h0 : ω 0 = i)
    (ht : returnTime i ω = ⊤) : visitCount i ω = 1 := by
  classical
  have hno : ∀ k : ℕ, k ≠ 0 → ω k ≠ i := by
    intro k hk hki
    have hf := (positiveReturnTime_finite_iff coordinate i ω).mpr
      ⟨k, by omega, hki⟩
    change returnTime i ω < ⊤ at hf
    rw [ht] at hf
    exact lt_irrefl _ hf
  unfold visitCount
  rw [tsum_eq_single 0]
  · simp [h0]
  · intro k hk
    simp [hno k hk]

theorem visitCount_of_returnTime_finite (i : S) (ω : ℕ → S) (h0 : ω 0 = i)
    (n : ℕ) (hn : returnTime i ω = n) :
    visitCount i ω = 1 + visitCount i (fun k => ω (n + k)) := by
  classical
  obtain ⟨h1, _, hno⟩ := returnTime_at_finite i ω n hn
  let f : ℕ → ℝ≥0∞ := fun k => if ω k = i then 1 else 0
  have he : visitCount i ω = ∑' k, f k := by simp [visitCount, f, Set.indicator_apply]
  have hs : (∑ k ∈ Finset.range n, f k) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [f, h0]
    · intro k hk hk0
      simp [f, hno k (by omega) (Finset.mem_range.mp hk)]
    · intro hn0
      exact (hn0 (Finset.mem_range.mpr h1)).elim
  rw [he, (ENNReal.summable.hasSum (f := fun k => f (k + n))).sum_range_add.tsum_eq, hs]
  congr 1
  apply tsum_congr
  intro k
  simp [f, Set.indicator_apply, Nat.add_comm]

theorem one_le_visitCount (i : S) (ω : ℕ → S) (h0 : ω 0 = i) :
    1 ≤ visitCount i ω := by
  have h := ENNReal.le_tsum (f := fun n : ℕ =>
    ({p : ℕ → S | p n = i}).indicator (fun _ => (1 : ℝ≥0∞)) ω) 0
  simpa [h0, visitCount] using h

/-- Removing the first visit leaves the shifted chain on the finite return event. -/
theorem visitCount_tail_return (i : S) (ω : ℕ → S) (h0 : ω 0 = i) (k : ℕ) :
    (k + 2 : ℝ≥0∞) ≤ visitCount i ω ↔
      returnTime i ω < ⊤ ∧ (k + 1 : ℝ≥0∞) ≤
        visitCount i (shiftedPath coordinate (returnTime i) (fun _ => i) ω) := by
  by_cases ht : returnTime i ω = ⊤
  · rw [visitCount_of_returnTime_top i ω h0 ht]
    have hk : ¬ (k + 2 : ℝ≥0∞) ≤ 1 := by exact_mod_cast (by omega : ¬ k + 2 ≤ 1)
    simp [ht, hk]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [visitCount_of_returnTime_finite i ω h0 n hn.symm,
      shiftedPath_at_finite coordinate (returnTime i) (fun _ => i) n ω hn.symm]
    have hfin : returnTime i ω < ⊤ := lt_top_iff_ne_top.mpr ht
    rw [and_iff_right hfin]
    change (k + 2 : ℝ≥0∞) ≤ 1 + visitCount i (fun m => ω (n + m)) ↔ _
    have he : (k + 2 : ℝ≥0∞) = 1 + (k + 1 : ℝ≥0∞) := by
      calc
        _ = (k : ℝ≥0∞) + 1 + 1 := by rw [add_assoc, one_add_one_eq_two]
        _ = _ := by ac_rfl
    rw [he, ENNReal.add_le_add_iff_left (by simp)]
    rfl

/-- The state at time zero is the prescribed initial state almost surely. -/
theorem statePathLaw_initial (P : StochasticMatrix S) (i : S) :
    ∀ᵐ ω ∂statePathLaw P i, ω 0 = i := by
  letI : Nonempty S := ⟨i⟩
  apply (mem_ae_iff_prob_eq_one (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)).mpr
  simpa [coordinate, statePathLaw] using (coordinate_isMarkovChain P (PMF.pure i)).2.1 i

/-- Strong Markov at the first positive return gives the tail recursion. -/
theorem visitCount_tail_step (P : StochasticMatrix S) (i : S) (k : ℕ) :
    statePathLaw P i {ω | (k + 2 : ℝ≥0∞) ≤ visitCount i ω} =
      statePathLaw P i {ω | (k + 1 : ℝ≥0∞) ≤ visitCount i ω} * returnProbability P i := by
  classical
  letI : Nonempty S := ⟨i⟩
  let τ := returnTime i
  let shift := shiftedPath coordinate τ (fun _ => i)
  let B : Set (ℕ → S) := {ω | (k + 1 : ℝ≥0∞) ≤ visitCount i ω}
  let F : Set (ℕ → S) := {ω | τ ω < ⊤}
  let g : (ℕ → S) → ℝ≥0∞ := B.indicator (fun _ => 1)
  have hB : MeasurableSet B := measurableSet_le measurable_const (measurable_visitCount i)
  have hF : MeasurableSet F := measurableSet_returnTime_finite i
  have hs : Measurable shift :=
    (measurable_shiftedPath coordinate coordinateFiltration
      (coordinate_isMarkovChain P (PMF.pure i)).1 τ (returnTime_isStoppingTime i)
      (fun _ => i)).mono (P207.terminalSigma_le _) le_rfl
  have hpre : MeasurableSet (shift ⁻¹' B) := hB.preimage hs
  have hg : Measurable g := measurable_const.indicator hB
  have hmark := strong_future_lintegral P (PMF.pure i) coordinate coordinateFiltration
    (statePathLaw P i) (coordinate_isMarkovChain P (PMF.pure i))
    τ (returnTime_isStoppingTime i) (fun _ => i) i g hg Set.univ MeasurableSet.univ
  simp only [Set.univ_inter] at hmark
  have hstop : ∀ ω ∈ F, stoppedState coordinate τ i ω = i := by
    intro ω hω
    change τ ω < ⊤ at hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω.ne
    rw [stoppedState_at_finite coordinate τ i n ω hn.symm]
    exact (returnTime_at_finite i ω n hn.symm).2.1
  have hright : (∫⁻ ω in F, ∫⁻ p, g p ∂statePathLaw P (stoppedState coordinate τ i ω)
      ∂statePathLaw P i) = statePathLaw P i B * returnProbability P i := by
    calc
      _ = ∫⁻ _ω in F, statePathLaw P i B ∂statePathLaw P i := by
        apply setLIntegral_congr_fun hF
        intro ω hω
        dsimp only
        rw [hstop ω hω]
        simp [g, lintegral_indicator hB]
      _ = _ := by simp [F, τ, returnProbability]
  have hleft : (∫⁻ ω in F, g (shift ω) ∂statePathLaw P i) =
      statePathLaw P i (F ∩ shift ⁻¹' B) := by
    have he : (fun ω => g (shift ω)) = (shift ⁻¹' B).indicator (fun _ => 1) := by
      funext ω
      simp [g, Set.indicator_apply]
    rw [he, lintegral_indicator hpre, lintegral_one]
    simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Measure.restrict_apply hpre, Set.inter_comm]
  have hevent : statePathLaw P i {ω | (k + 2 : ℝ≥0∞) ≤ visitCount i ω} =
      statePathLaw P i (F ∩ shift ⁻¹' B) := by
    apply measure_congr
    filter_upwards [statePathLaw_initial P i] with ω hω
    exact propext (visitCount_tail_return i ω hω k)
  exact hevent.trans (hleft.symm.trans (hmark.trans hright))

theorem visitCount_tail_succ (P : StochasticMatrix S) (i : S) (k : ℕ) :
    statePathLaw P i {ω | (k + 1 : ℝ≥0∞) ≤ visitCount i ω} = returnProbability P i ^ k := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_add, pow_zero]
    apply (mem_ae_iff_prob_eq_one
      (measurableSet_le measurable_const (measurable_visitCount i))).mp
    filter_upwards [statePathLaw_initial P i] with ω hω
    exact one_le_visitCount i ω hω
  | succ k ih =>
    have he : ((k + 1 : ℕ) + 1 : ℝ≥0∞) = (k + 2 : ℝ≥0∞) := by
      simp only [Nat.cast_add, Nat.cast_one]
      rw [add_assoc, one_add_one_eq_two]
    rw [he, visitCount_tail_step, ih, pow_succ]

theorem visitCount_tail (P : StochasticMatrix S) (i : S) (k : ℕ) (hk : 1 ≤ k) :
    statePathLaw P i {ω | (k : ℝ≥0∞) ≤ visitCount i ω} =
      returnProbability P i ^ (k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simpa using visitCount_tail_succ P i n

/-- The geometric-series identity is valid even when the return probability is one. -/
theorem meanVisits_eq_geometric (P : StochasticMatrix S) (i : S) :
    meanVisits P i = (1 - returnProbability P i)⁻¹ := by
  rw [meanVisits_eq_tsum_tails]
  simp_rw [visitCount_tail_succ]
  exact ENNReal.tsum_geometric _

theorem meanVisits_eq_inv (P : StochasticMatrix S) (i : S)
    (_h : returnProbability P i < 1) :
    meanVisits P i = (1 - returnProbability P i)⁻¹ := meanVisits_eq_geometric P i

theorem meanVisits_eq_top (P : StochasticMatrix S) (i : S) (h : Recurrent P i) :
    meanVisits P i = ⊤ := by
  rw [meanVisits_eq_geometric, h, tsub_self, ENNReal.inv_zero]

theorem recurrent_iff_greenSeries_eq_top (P : StochasticMatrix S) (i : S) :
    Recurrent P i ↔ greenSeries P i = ⊤ := by
  rw [greenSeries_eq_meanVisits, meanVisits_eq_geometric, ENNReal.inv_eq_top,
    tsub_eq_zero_iff_le]
  exact ⟨fun h => h.ge, fun h => le_antisymm (returnProbability_le_one P i) h⟩

theorem transient_iff_greenSeries_lt_top (P : StochasticMatrix S) (i : S) :
    Transient P i ↔ greenSeries P i < ⊤ := by
  rw [transient_iff_not_recurrent, recurrent_iff_greenSeries_eq_top, lt_top_iff_ne_top]

theorem recurrent_infinite_visits (P : StochasticMatrix S) (i : S) (h : Recurrent P i) :
    ∀ᵐ ω ∂statePathLaw P i, visitCount i ω = ⊤ := by
  have ht (n : ℕ) : ∀ᵐ ω ∂statePathLaw P i, (n + 1 : ℝ≥0∞) ≤ visitCount i ω := by
    apply (mem_ae_iff_prob_eq_one
      (measurableSet_le measurable_const (measurable_visitCount i))).mpr
    rw [visitCount_tail_succ, h, one_pow]
  filter_upwards [ae_all_iff.mpr ht] with ω hω
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  exact iSup_le fun n => (le_add_right le_rfl).trans (hω n)

theorem chain_visitCount_tail [Nonempty S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (i : S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P (PMF.pure i) X ℱ μ) (k : ℕ) (hk : 1 ≤ k) :
    μ {ω | (k : ℝ≥0∞) ≤ visitCount i (fun n => X n ω)} =
      returnProbability P i ^ (k - 1) := by
  have hp : Measurable (fun ω n => X n ω) := Measurable.of_eval (fun n => h.1.measurable)
  have hB : MeasurableSet {ω : ℕ → S | (k : ℝ≥0∞) ≤ visitCount i ω} :=
    measurableSet_le measurable_const (measurable_visitCount i)
  change μ ((fun ω n => X n ω) ⁻¹' {p : ℕ → S | (k : ℝ≥0∞) ≤ visitCount i p}) = _
  rw [← Measure.map_apply hp hB, chain_pathLaw P (PMF.pure i) X ℱ μ h]
  exact visitCount_tail P i k hk

theorem chain_recurrent_infinite_visits [Nonempty S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (i : S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P (PMF.pure i) X ℱ μ) (hr : Recurrent P i) :
    ∀ᵐ ω ∂μ, visitCount i (fun n => X n ω) = ⊤ := by
  have hp : Measurable (fun ω n => X n ω) := Measurable.of_eval (fun n => h.1.measurable)
  have ht (n : ℕ) : ∀ᵐ ω ∂μ, (n + 1 : ℝ≥0∞) ≤ visitCount i (fun m => X m ω) := by
    apply (mem_ae_iff_prob_eq_one
      (measurableSet_le measurable_const ((measurable_visitCount i).comp hp))).mpr
    have htail := chain_visitCount_tail P i X ℱ μ h (n + 1) (by omega)
    rw [show returnProbability P i = 1 from hr, one_pow] at htail
    simpa using htail
  filter_upwards [ae_all_iff.mpr ht] with ω hω
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  exact iSup_le fun n => (le_add_right le_rfl).trans (hω n)

end Discrete
end
end P207.Markov
