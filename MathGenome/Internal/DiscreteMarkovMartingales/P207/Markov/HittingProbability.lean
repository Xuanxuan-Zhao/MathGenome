import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.HittingProbability
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.FixedFutureLaw
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.DeterministicTransitions
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal MeasureTheory

set_option linter.unusedSectionVars false
universe u
namespace P207.Markov
noncomputable section

namespace HittingProbability
abbrev hittingTime : HittingProbabilitySpec.hittingTimeType.{u} := @P207.Markov.hittingTime
abbrev hittingProbability : HittingProbabilitySpec.hittingProbabilityType.{u} :=
  @P207.Markov.hittingProbability
end HittingProbability

theorem hittingTime_le_iff {S : Type u} (A : Set S) (ω : ℕ → S) (n : ℕ) :
    hittingTime A ω ≤ n ↔ ∃ k ≤ n, ω k ∈ A := by
  simpa [hittingTime, coordinate] using
    (hittingAfter_le_iff (u := coordinate) (s := A) (n := 0) (ω := ω) (i := n))

theorem hittingTime_finite_iff {S : Type u} (A : Set S) (ω : ℕ → S) :
    hittingTime A ω < ⊤ ↔ ∃ k : ℕ, ω k ∈ A := by
  rw [lt_top_iff_ne_top]
  simp [hittingTime, hittingAfter_eq_top_iff, coordinate]

section Measurability
variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem hittingTime_isStoppingTime (A : Set S) :
    P207.IsDiscreteStoppingTime coordinateFiltration (hittingTime A) := by
  exact (P207.adapted_naturalFiltration coordinate (fun n => measurable_pi_apply n)).isStoppingTime_hittingAfter
    (Set.to_countable A).measurableSet

/-- Both the finite-horizon and eventual hitting events are measurable. -/
theorem measurableSet_hittingTime_le (A : Set S) (n : ℕ) :
    MeasurableSet {ω : ℕ → S | hittingTime A ω ≤ n} :=
  (coordinateFiltration (S := S)).le n _ (hittingTime_isStoppingTime A n)

theorem measurableSet_hittingTime_finite (A : Set S) :
    MeasurableSet {ω : ℕ → S | hittingTime A ω < ⊤} := by
  have he : {ω : ℕ → S | hittingTime A ω < ⊤} = ⋃ n : ℕ, {ω | ω n ∈ A} := by
    ext ω
    simp [hittingTime_finite_iff]
  rw [he]
  exact MeasurableSet.iUnion fun n => (measurable_pi_apply n) (Set.to_countable A).measurableSet

end Measurability

variable {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S]

local instance hitting_statePathLaw_probability (P : StochasticMatrix S) (i : S) :
    IsProbabilityMeasure (statePathLaw P i) := pathLaw_probability P (PMF.pure i)

local instance hitting_pathKernel_isMarkov (P : StochasticMatrix S) :
    IsMarkovKernel (pathKernel P) := pathKernel_markov P

theorem hittingProbability_le_one (P : StochasticMatrix S) (A : Set S) (i : S) :
    hittingProbability P A i ≤ 1 := prob_le_one

/-- Under a point-mass initial law the time-zero coordinate equals the initial state. -/
theorem coordinate_zero_ae (P : StochasticMatrix S) (i : S) :
    ∀ᵐ ω ∂statePathLaw P i, ω 0 = i := by
  apply (mem_ae_iff_prob_eq_one
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)).mpr
  have h := (coordinate_isMarkovChain P (PMF.pure i)).2.1 i
  simpa [coordinate, statePathLaw, PMF.pure_apply] using h

theorem hittingProbability_boundary (P : StochasticMatrix S) (A : Set S) (i : S)
    (hi : i ∈ A) : hittingProbability P A i = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_hittingTime_finite A)).mp
  filter_upwards [coordinate_zero_ae P i] with ω hω
  exact (hittingTime_finite_iff A ω).mpr ⟨0, hω ▸ hi⟩

theorem hittingProbability_empty (P : StochasticMatrix S) (i : S) :
    hittingProbability P ∅ i = 0 := by
  simp [hittingProbability, hittingTime, hittingAfter_empty]

theorem hittingProbability_univ (P : StochasticMatrix S) (i : S) :
    hittingProbability P Set.univ i = 1 :=
  hittingProbability_boundary P Set.univ i (Set.mem_univ i)

/-- First-step disintegration, for every measurable path event. -/
theorem hitting_first_step (P : StochasticMatrix S) (i : S)
    (B : Set (ℕ → S)) (hB : MeasurableSet B) :
    statePathLaw P i {ω | (fun k => ω (1 + k)) ∈ B} =
      ∑' j, P i j * statePathLaw P j B := by
  have hc := coordinate_isMarkovChain P (PMF.pure i)
  let K := (pathKernel P).comap (coordinate 1) (measurable_pi_apply 1)
  have hm := FixedFutureLaw.future_measure hc 1 Set.univ MeasurableSet.univ
  rw [Measure.restrict_univ] at hm
  change (statePathLaw P i).map (fun ω k => ω (1 + k)) = K ∘ₘ statePathLaw P i at hm
  have he := congrArg (fun ρ : Measure (ℕ → S) => ρ B) hm
  rw [Measure.map_apply (measurable_pi_iff.mpr (fun k => measurable_pi_apply (1 + k))) hB,
    Measure.bind_apply hB K.aemeasurable] at he
  change statePathLaw P i {ω | (fun k => ω (1 + k)) ∈ B} =
    ∫⁻ ω, statePathLaw P (ω 1) B ∂statePathLaw P i at he
  rw [he]
  have hf : Measurable (fun j => statePathLaw P j B) := measurable_of_countable _
  rw [← lintegral_map hf (measurable_pi_apply 1), lintegral_countable']
  apply tsum_congr
  intro j
  rw [Measure.map_apply (measurable_pi_apply 1) (measurableSet_singleton j)]
  have hj := DeterministicTransitions.marginal_mass hc 1 j
  change statePathLaw P i {ω | ω 1 = j} = _ at hj
  change statePathLaw P j B * statePathLaw P i {ω | ω 1 = j} = _
  rw [hj]
  simp [evolve, power_one, PMF.pure_bind, mul_comm]

theorem hittingProbability_harmonic (P : StochasticMatrix S) (A : Set S) (i : S)
    (hi : i ∉ A) : hittingProbability P A i = action P (hittingProbability P A) i := by
  unfold hittingProbability action
  rw [← hitting_first_step P i _ (measurableSet_hittingTime_finite A)]
  apply measure_congr
  filter_upwards [coordinate_zero_ae P i] with ω hω
  apply propext
  simp only [hittingTime_finite_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact (hi (hω ▸ hn)).elim
    | succ n => exact ⟨n, by simpa [Nat.add_comm] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨1 + n, hn⟩

/-- Finite-horizon hitting probabilities satisfy the same first-step recursion. -/
theorem hittingTime_cutoff_step (P : StochasticMatrix S) (A : Set S) (i : S)
    (hi : i ∉ A) (N : ℕ) :
    statePathLaw P i {ω | hittingTime A ω ≤ (N + 1 : ℕ)} =
      ∑' j, P i j * statePathLaw P j {ω | hittingTime A ω ≤ N} := by
  rw [← hitting_first_step P i _ (measurableSet_hittingTime_le A N)]
  apply measure_congr
  filter_upwards [coordinate_zero_ae P i] with ω hω
  apply propext
  simp only [hittingTime_le_iff]
  constructor
  · rintro ⟨n, hn, hnA⟩
    cases n with
    | zero => exact (hi (hω ▸ hnA)).elim
    | succ n => exact ⟨n, Nat.le_of_succ_le_succ hn, by simpa [Nat.add_comm] using hnA⟩
  · rintro ⟨n, hn, hnA⟩
    exact ⟨1 + n, by omega, hnA⟩

/-- Finite-horizon domination uses no boundedness assumption on the candidate solution. -/
theorem hittingTime_cutoff_le (P : StochasticMatrix S) (A : Set S) (v : S → ℝ≥0∞)
    (hA : ∀ i ∈ A, v i = 1) (hv : ∀ i, i ∉ A → v i = action P v i)
    (N : ℕ) (i : S) : statePathLaw P i {ω | hittingTime A ω ≤ N} ≤ v i := by
  induction N generalizing i with
  | zero =>
    by_cases hi : i ∈ A
    · rw [hA i hi]
      exact prob_le_one
    · have he : statePathLaw P i {ω | hittingTime A ω ≤ (0 : ℕ)} = 0 := by
        rw [← measure_empty (μ := statePathLaw P i)]
        apply measure_congr
        filter_upwards [coordinate_zero_ae P i] with ω hω
        change (hittingTime A ω ≤ (0 : ℕ)) = False
        apply propext
        rw [hittingTime_le_iff]
        simp [hω, hi]
      rw [he]
      exact zero_le
  | succ N ih =>
    by_cases hi : i ∈ A
    · rw [hA i hi]
      exact prob_le_one
    · rw [hittingTime_cutoff_step P A i hi N, hv i hi]
      exact ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (ih j)

theorem hittingProbability_least (P : StochasticMatrix S) (A : Set S) (v : S → ℝ≥0∞)
    (hA : ∀ i ∈ A, v i = 1) (hv : ∀ i, i ∉ A → v i = action P v i)
    (i : S) : hittingProbability P A i ≤ v i := by
  have he : {ω : ℕ → S | hittingTime A ω < ⊤} =
      ⋃ N : ℕ, {ω | hittingTime A ω ≤ N} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hittingTime_finite_iff, hittingTime_le_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩, fun ⟨N, n, _, hn⟩ => ⟨n, hn⟩⟩
  have hm : Monotone (fun N : ℕ => {ω : ℕ → S | hittingTime A ω ≤ N}) := by
    intro N M hNM ω hω
    exact hω.trans (WithTop.coe_le_coe.mpr hNM)
  rw [hittingProbability, he, hm.measure_iUnion]
  exact iSup_le fun N => hittingTime_cutoff_le P A v hA hv N i

end
end P207.Markov
