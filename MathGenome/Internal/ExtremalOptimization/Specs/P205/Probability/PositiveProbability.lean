import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.FiniteModels

/-! Independent statements of Proposition 4.1 (`p205:W14`), paper.tex 759–772.
The decoding conclusion retains the outcome in the event, so the object is
explicitly a realized value of the given decoding map. -/

open MeasureTheory

namespace P205.Probability.PositiveProbabilitySpec

def eventNonempty : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω), MeasurableSet A → 0 < μ A → A.Nonempty

def decodedWitness : Prop :=
  ∀ {Ω C : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (f : Ω → C) (Q : C → Prop),
    MeasurableSet A → 0 < μ A → (∀ c ∈ f '' A, Q c) →
    ∃ ω ∈ A, Q (f ω)

def finitePositiveWitness : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω) (A : Set Ω),
    0 < M.eventMass A → ∃ ω ∈ A, 0 < M.weight ω

def finiteDecodedWitness : Prop :=
  ∀ {Ω C : Type*} [Fintype Ω] (M : FiniteModel Ω)
    (A : Set Ω) (f : Ω → C) (Q : C → Prop),
    0 < M.eventMass A → (∀ c ∈ f '' A, Q c) →
    ∃ ω ∈ A, 0 < M.weight ω ∧ Q (f ω)

def finiteMeasurePositiveWitness : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (M : FiniteModel Ω) (A : Set Ω),
    0 < M.measure A → ∃ ω ∈ A, 0 < M.weight ω

def finiteMeasureDecodedWitness : Prop :=
  ∀ {Ω C : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (M : FiniteModel Ω) (A : Set Ω) (f : Ω → C) (Q : C → Prop),
    0 < M.measure A → (∀ c ∈ f '' A, Q c) →
    ∃ ω ∈ A, 0 < M.weight ω ∧ Q (f ω)

end P205.Probability.PositiveProbabilitySpec
