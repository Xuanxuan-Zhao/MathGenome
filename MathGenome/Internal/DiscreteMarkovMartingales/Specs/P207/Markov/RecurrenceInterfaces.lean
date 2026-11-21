import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.HittingProbability
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open MeasureTheory
open scoped ENNReal MeasureTheory
universe u v
namespace P207.Markov
noncomputable section

/-- Canonical recurrence and period objects; infinity is retained in the mean. -/
def Accessible {S : Type u} (P : StochasticMatrix S) (i j : S) : Prop :=
  ∃ n : ℕ, 0 < power P n i j

def Communicate {S : Type u} (P : StochasticMatrix S) (i j : S) : Prop :=
  Accessible P i j ∧ Accessible P j i

def communicatingClass {S : Type u} (P : StochasticMatrix S) (i : S) : Set S :=
  {j | Communicate P i j}

def IsCommunicatingClass {S : Type u} (P : StochasticMatrix S) (C : Set S) : Prop :=
  ∃ i, C = communicatingClass P i

def Irreducible {S : Type u} (P : StochasticMatrix S) : Prop :=
  ∀ i j, Communicate P i j

def IsClosed {S : Type u} (P : StochasticMatrix S) (C : Set S) : Prop :=
  ∀ i ∈ C, ∀ j, 0 < P i j → j ∈ C

def IsClosedCommunicatingClass {S : Type u} (P : StochasticMatrix S) (C : Set S) : Prop :=
  IsCommunicatingClass P C ∧ IsClosed P C

def positiveReturnTime {S : Type u} {Ω : Type v} (X : ℕ → Ω → S) (i : S) : Ω → WithTop ℕ :=
  hittingAfter X {i} 1

def returnTime {S : Type u} (i : S) : (ℕ → S) → WithTop ℕ :=
  positiveReturnTime coordinate i

def returnProbability {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S) : ℝ≥0∞ :=
  statePathLaw P i {ω | returnTime i ω < ⊤}

def meanReturnTime {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S) : ℝ≥0∞ :=
  ∫⁻ ω, ENat.toENNReal (returnTime i ω) ∂statePathLaw P i

def Recurrent {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S) : Prop :=
  returnProbability P i = 1

def Transient {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S) : Prop :=
  returnProbability P i < 1

def PositiveRecurrent {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S) : Prop :=
  meanReturnTime P i < ⊤

def NullRecurrent {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S) : Prop :=
  Recurrent P i ∧ meanReturnTime P i = ⊤

def returnLengths {S : Type u} (P : StochasticMatrix S) (i : S) : Set ℕ :=
  {n | 1 ≤ n ∧ 0 < power P n i i}

def period {S : Type u} (P : StochasticMatrix S) (i : S) : ℕ :=
  Nat.setGcd (returnLengths P i)

def Aperiodic {S : Type u} (P : StochasticMatrix S) (i : S) : Prop :=
  period P i = 1

namespace RecurrenceInterfacesSpec

def AccessibleType := {S : Type u} → StochasticMatrix S → S → S → Prop
def AccessibleValue : AccessibleType := @P207.Markov.Accessible

def CommunicateType := {S : Type u} → StochasticMatrix S → S → S → Prop
def CommunicateValue : CommunicateType := @P207.Markov.Communicate

def communicatingClassType := {S : Type u} → StochasticMatrix S → S → Set S
def communicatingClassValue : communicatingClassType := @P207.Markov.communicatingClass

def IsCommunicatingClassType := {S : Type u} → StochasticMatrix S → Set S → Prop
def IsCommunicatingClassValue : IsCommunicatingClassType := @P207.Markov.IsCommunicatingClass

def IrreducibleType := {S : Type u} → StochasticMatrix S → Prop
def IrreducibleValue : IrreducibleType := @P207.Markov.Irreducible

def IsClosedType := {S : Type u} → StochasticMatrix S → Set S → Prop
def IsClosedValue : IsClosedType := @P207.Markov.IsClosed

def IsClosedCommunicatingClassType := {S : Type u} → StochasticMatrix S → Set S → Prop
def IsClosedCommunicatingClassValue : IsClosedCommunicatingClassType := @P207.Markov.IsClosedCommunicatingClass

def positiveReturnTimeType := {S : Type u} → {Ω : Type v} → (ℕ → Ω → S) → S → Ω → WithTop ℕ
def positiveReturnTimeValue : positiveReturnTimeType := @P207.Markov.positiveReturnTime

def returnTimeType := {S : Type u} → S → (ℕ → S) → WithTop ℕ
def returnTimeValue : returnTimeType := @P207.Markov.returnTime

def returnProbabilityType := {S : Type u} → [Countable S] → [MeasurableSpace S] → [DiscreteMeasurableSpace S] → StochasticMatrix S → S → ℝ≥0∞
def returnProbabilityValue : returnProbabilityType := @P207.Markov.returnProbability

def meanReturnTimeType := {S : Type u} → [Countable S] → [MeasurableSpace S] → [DiscreteMeasurableSpace S] → StochasticMatrix S → S → ℝ≥0∞
def meanReturnTimeValue : meanReturnTimeType := @P207.Markov.meanReturnTime

def RecurrentType := {S : Type u} → [Countable S] → [MeasurableSpace S] → [DiscreteMeasurableSpace S] → StochasticMatrix S → S → Prop
def RecurrentValue : RecurrentType := @P207.Markov.Recurrent

def TransientType := {S : Type u} → [Countable S] → [MeasurableSpace S] → [DiscreteMeasurableSpace S] → StochasticMatrix S → S → Prop
def TransientValue : TransientType := @P207.Markov.Transient

def PositiveRecurrentType := {S : Type u} → [Countable S] → [MeasurableSpace S] → [DiscreteMeasurableSpace S] → StochasticMatrix S → S → Prop
def PositiveRecurrentValue : PositiveRecurrentType := @P207.Markov.PositiveRecurrent

def NullRecurrentType := {S : Type u} → [Countable S] → [MeasurableSpace S] → [DiscreteMeasurableSpace S] → StochasticMatrix S → S → Prop
def NullRecurrentValue : NullRecurrentType := @P207.Markov.NullRecurrent

def returnLengthsType := {S : Type u} → StochasticMatrix S → S → Set ℕ
def returnLengthsValue : returnLengthsType := @P207.Markov.returnLengths

def periodType := {S : Type u} → StochasticMatrix S → S → ℕ
def periodValue : periodType := @P207.Markov.period

def AperiodicType := {S : Type u} → StochasticMatrix S → S → Prop
def AperiodicValue : AperiodicType := @P207.Markov.Aperiodic

def accessible_refl : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i : S),
    Accessible P i i

def accessible_trans : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) {i j k : S}
    (hij : Accessible P i j) (hjk : Accessible P j k),
    Accessible P i k

def communicate_equivalence : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S),
    Equivalence (Communicate P)

def isClosed_iff : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (C : Set S),
    IsClosed P C ↔ ∀ i ∈ C, ∀ j ∉ C, P i j = 0

def positiveReturnTime_le_iff : Prop :=
  ∀ {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (ω : Ω) (n : ℕ),
    positiveReturnTime X i ω ≤ n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ X k ω = i

def positiveReturnTime_finite_iff : Prop :=
  ∀ {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (ω : Ω),
    positiveReturnTime X i ω < ⊤ ↔ ∃ k : ℕ, 1 ≤ k ∧ X k ω = i

def positiveReturnTime_isStoppingTime : Prop :=
  ∀ {S : Type u} [MeasurableSpace S]
    [MeasurableSingletonClass S] {Ω : Type v} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (hX : Adapted ℱ X) (i : S),
    P207.IsDiscreteStoppingTime ℱ (positiveReturnTime X i)

def returnTime_isStoppingTime : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (i : S),
    P207.IsDiscreteStoppingTime coordinateFiltration (returnTime i)

def measurableSet_returnTime_finite : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (i : S),
    MeasurableSet {ω : ℕ → S | returnTime i ω < ⊤}

def measurable_returnTime : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (i : S),
    Measurable (returnTime i)

def measurable_returnDuration : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (i : S),
    Measurable (fun ω : ℕ → S => ENat.toENNReal (returnTime i ω))

def returnProbability_le_one : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
    returnProbability P i ≤ 1

def positiveRecurrent_recurrent : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S)
    (h : PositiveRecurrent P i),
    Recurrent P i

def transient_iff_not_recurrent : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
    Transient P i ↔ ¬ Recurrent P i

def period_eq_zero_iff : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i : S),
    period P i = 0 ↔ returnLengths P i = ∅

def period_dvd_returnLength : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i : S)
    (n : ℕ) (hn : n ∈ returnLengths P i),
    period P i ∣ n

def dvd_period_iff : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i : S) (d : ℕ),
    d ∣ period P i ↔ ∀ n ∈ returnLengths P i, d ∣ n

end RecurrenceInterfacesSpec
end
end P207.Markov
