import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.ClosedRecurrentClasses
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.ClassRecurrence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.HittingProbability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal MeasureTheory
universe u
namespace P207.Markov
noncomputable section

variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

local instance (P : StochasticMatrix S) (i : S) : IsProbabilityMeasure (statePathLaw P i) := by
  unfold statePathLaw
  infer_instance

/-- Disintegration of the future at any deterministic time. -/
theorem future_event_mass (P : StochasticMatrix S) (i : S) (n : ℕ)
    (B : Set (ℕ → S)) (hB : MeasurableSet B) :
    statePathLaw P i {ω | (fun k => ω (n + k)) ∈ B} =
      ∑' j, power P n i j * statePathLaw P j B := by
  letI : Nonempty S := ⟨i⟩
  letI : IsMarkovKernel (pathKernel P) := pathKernel_markov P
  have hc := coordinate_isMarkovChain P (PMF.pure i)
  let K := (pathKernel P).comap (coordinate n) (measurable_pi_apply n)
  have hm := FixedFutureLaw.future_measure hc n Set.univ MeasurableSet.univ
  rw [Measure.restrict_univ] at hm
  change (statePathLaw P i).map (fun ω k => ω (n + k)) = K ∘ₘ statePathLaw P i at hm
  have he := congrArg (fun ρ : Measure (ℕ → S) => ρ B) hm
  rw [Measure.map_apply (measurable_pi_iff.mpr (fun k => measurable_pi_apply (n + k))) hB,
    Measure.bind_apply hB K.aemeasurable] at he
  change statePathLaw P i {ω | (fun k => ω (n + k)) ∈ B} =
    ∫⁻ ω, statePathLaw P (ω n) B ∂statePathLaw P i at he
  rw [he]
  have hf : Measurable (fun j => statePathLaw P j B) := measurable_of_countable _
  rw [← lintegral_map hf (measurable_pi_apply n), lintegral_countable']
  apply tsum_congr
  intro j
  rw [Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton j)]
  have hj := DeterministicTransitions.marginal_mass hc n j
  change statePathLaw P i {ω | ω n = j} = _ at hj
  change statePathLaw P j B * statePathLaw P i {ω | ω n = j} = _
  rw [hj]
  simp [evolve, PMF.pure_bind, mul_comm]

/-- Positive eventual hitting entails a positive transition power. -/
theorem accessible_of_hittingProbability_ne_zero (P : StochasticMatrix S) (i j : S)
    (h : hittingProbability P {j} i ≠ 0) : Accessible P i j := by
  letI : Nonempty S := ⟨i⟩
  by_contra hn
  have hz (n : ℕ) : power P n i j = 0 := by
    exact le_antisymm (not_lt.mp (fun hp => hn ⟨n, hp⟩)) zero_le
  have hm (n : ℕ) : statePathLaw P i {ω | ω n = j} = 0 := by
    have he := DeterministicTransitions.marginal_mass
      (coordinate_isMarkovChain P (PMF.pure i)) n j
    simpa [coordinate, statePathLaw, evolve, PMF.pure_bind, hz n] using he
  apply h
  have he : {ω : ℕ → S | hittingTime {j} ω < ⊤} = ⋃ n : ℕ, {ω | ω n = j} := by
    ext ω
    simp [hittingTime_finite_iff]
  rw [hittingProbability, he]
  exact measure_iUnion_null hm

/-- Every reachable state hits the recurrent starting state almost surely.
Infinite visits leave a visit after every fixed time; disintegration at that
fixed time rules out a positive probability of never hitting from a reachable state. -/
theorem hittingProbability_recurrent_of_accessible (P : StochasticMatrix S) {i j : S}
    (hi : Recurrent P i) (hij : Accessible P i j) :
    hittingProbability P {i} j = 1 := by
  letI : Nonempty S := ⟨i⟩
  obtain ⟨n, hn⟩ := hij
  let B : Set (ℕ → S) := {ω | hittingTime {i} ω < ⊤}ᶜ
  have hB : MeasurableSet B := (measurableSet_hittingTime_finite {i}).compl
  have hnull : statePathLaw P i {ω | (fun k => ω (n + k)) ∈ B} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [recurrent_infinite_visits P i hi] with ω hω
    obtain ⟨m, hm, hnm⟩ := ((visitCount_eq_top_iff i ω).mp hω).exists_gt n
    change ¬ ¬ hittingTime {i} (fun k => ω (n + k)) < ⊤
    apply not_not.mpr
    apply (hittingTime_finite_iff _ _).mpr
    exact ⟨m - n, by simpa [Nat.add_sub_of_le hnm.le] using hm⟩
  have hz : power P n i j * statePathLaw P j B = 0 := by
    apply le_antisymm _ zero_le
    exact (ENNReal.le_tsum (f := fun k => power P n i k * statePathLaw P k B) j).trans
      (le_of_eq ((future_event_mass P i n B hB).symm.trans hnull))
  have hb : statePathLaw P j B = 0 := (mul_eq_zero.mp hz).resolve_left hn.ne'
  apply (mem_ae_iff_prob_eq_one (measurableSet_hittingTime_finite {i})).mp
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hb] with ω hω
  exact not_not.mp hω


/-- A recurrent state cannot reach a state outside its communication class. -/
theorem communicate_of_recurrent_accessible (P : StochasticMatrix S) {i j : S}
    (hi : Recurrent P i) (hij : Accessible P i j) : Communicate P i j := by
  refine ⟨hij, accessible_of_hittingProbability_ne_zero P j i ?_⟩
  rw [hittingProbability_recurrent_of_accessible P hi hij]
  exact one_ne_zero

/-- Members of a communicating class communicate with each other. -/
theorem communicate_of_class_members (P : StochasticMatrix S) {C : Set S}
    (hC : IsCommunicatingClass P C) {i j : S} (hi : i ∈ C) (hj : j ∈ C) :
    Communicate P i j := by
  obtain ⟨r, rfl⟩ := hC
  exact (communicate_equivalence P).trans ((communicate_equivalence P).symm hi) hj

/-- All members inherit recurrence from any recurrent member of the class. -/
theorem recurrent_of_recurrent_class (P : StochasticMatrix S) {C : Set S}
    (hC : IsCommunicatingClass P C) (hr : ∃ r ∈ C, Recurrent P r)
    {i : S} (hi : i ∈ C) : Recurrent P i := by
  obtain ⟨r, hrC, hr⟩ := hr
  exact (recurrent_iff_of_communicate P (communicate_of_class_members P hC hrC hi)).mp hr

/-- Every communicating class containing a recurrent state is closed. -/
theorem recurrent_class_isClosed (P : StochasticMatrix S) (C : Set S)
    (hC : IsCommunicatingClass P C) (hr : ∃ r ∈ C, Recurrent P r) :
    IsClosed P C := by
  intro i hi j hij
  have ha : Accessible P i j := ⟨1, by simpa [power_one] using hij⟩
  have hc := communicate_of_recurrent_accessible P (recurrent_of_recurrent_class P hC hr hi) ha
  obtain ⟨r, rfl⟩ := hC
  exact (communicate_equivalence P).trans hi hc

/-- First hits include zero, so this also covers equal starting and target states. -/
theorem recurrent_class_hittingProbability (P : StochasticMatrix S) (C : Set S)
    (hC : IsCommunicatingClass P C) (hr : ∃ r ∈ C, Recurrent P r)
    (i : S) (hi : i ∈ C) (j : S) (hj : j ∈ C) :
    hittingProbability P {j} i = 1 := by
  exact hittingProbability_recurrent_of_accessible P
    (recurrent_of_recurrent_class P hC hr hj)
    (communicate_of_class_members P hC hj hi).1

end
end P207.Markov
