import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.PositiveProbability
import MathGenome.Internal.ExtremalOptimization.P205.Probability.FiniteModels

open MeasureTheory

namespace P205.Probability

/-- A positive-probability event contains an outcome (Proposition 4.1). -/
theorem nonempty_of_positive_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω)
    (_hA : MeasurableSet A) (hpos : 0 < μ A) : A.Nonempty :=
  nonempty_of_measure_ne_zero hpos.ne'

/-- Applying the decoding map to an event witness realizes the property. -/
theorem exists_decoded_of_positive_probability {Ω C : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (f : Ω → C) (Q : C → Prop)
    (hA : MeasurableSet A) (hpos : 0 < μ A) (hQ : ∀ c ∈ f '' A, Q c) :
    ∃ ω ∈ A, Q (f ω) := by
  obtain ⟨ω, hω⟩ := nonempty_of_positive_probability μ A hA hpos
  exact ⟨ω, hω, hQ (f ω) ⟨ω, hω, rfl⟩⟩

namespace FiniteModel

/-- A positive sum of nonnegative event weights has a positive summand. -/
theorem exists_positive_weight_of_eventMass_pos {Ω : Type*} [Fintype Ω]
    (M : FiniteModel Ω) (A : Set Ω) (hpos : 0 < M.eventMass A) :
    ∃ ω ∈ A, 0 < M.weight ω := by
  classical
  rw [eventMass_eq_sum] at hpos
  obtain ⟨ω, hω, hp⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun ω _ => M.weight_nonneg ω)).mp hpos
  exact ⟨ω, Set.mem_toFinset.mp hω, hp⟩

theorem exists_decoded_of_eventMass_pos {Ω C : Type*} [Fintype Ω]
    (M : FiniteModel Ω) (A : Set Ω) (f : Ω → C) (Q : C → Prop)
    (hpos : 0 < M.eventMass A) (hQ : ∀ c ∈ f '' A, Q c) :
    ∃ ω ∈ A, 0 < M.weight ω ∧ Q (f ω) := by
  obtain ⟨ω, hω, hp⟩ := exists_positive_weight_of_eventMass_pos M A hpos
  exact ⟨ω, hω, hp, hQ (f ω) ⟨ω, hω, rfl⟩⟩

/-- The same finite witness, with positivity stated in measure notation. -/
theorem exists_positive_weight_of_measure_pos {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (M : FiniteModel Ω) (A : Set Ω) (hpos : 0 < M.measure A) :
    ∃ ω ∈ A, 0 < M.weight ω := by
  rw [measure_eventMass, ENNReal.ofReal_pos] at hpos
  exact exists_positive_weight_of_eventMass_pos M A hpos

theorem exists_decoded_of_measure_pos {Ω C : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (M : FiniteModel Ω) (A : Set Ω) (f : Ω → C) (Q : C → Prop)
    (hpos : 0 < M.measure A) (hQ : ∀ c ∈ f '' A, Q c) :
    ∃ ω ∈ A, 0 < M.weight ω ∧ Q (f ω) := by
  obtain ⟨ω, hω, hp⟩ := exists_positive_weight_of_measure_pos M A hpos
  exact ⟨ω, hω, hp, hQ (f ω) ⟨ω, hω, rfl⟩⟩

end FiniteModel
end P205.Probability
