import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.FixedFutureLaw
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

universe u v
namespace P207.Markov
noncomputable section

/-- A state at a possibly infinite stopping time, with a specified fixed fallback. -/
def stoppedState {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (τ : Ω → WithTop ℕ) (iInf : S) (ω : Ω) : S :=
  if τ ω = ⊤ then iInf else X (τ ω).untopA ω

/-- The whole future starting at a finite stopping time. The infinite layer is
assigned a fixed path; no coordinate of the process at infinity is evaluated. -/
def shiftedPath {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (τ : Ω → WithTop ℕ) (pInf : ℕ → S) (ω : Ω) : ℕ → S :=
  if τ ω = ⊤ then pInf else fun k => X ((τ ω).untopA + k) ω

namespace StrongMarkovSpec

def stoppedStateType := {S : Type u} → {Ω : Type v} →
  (ℕ → Ω → S) → (Ω → WithTop ℕ) → S → Ω → S
def stoppedStateValue : stoppedStateType.{u,v} := @stoppedState

def shiftedPathType := {S : Type u} → {Ω : Type v} →
  (ℕ → Ω → S) → (Ω → WithTop ℕ) → (ℕ → S) → Ω → (ℕ → S)
def shiftedPathValue : shiftedPathType.{u,v} := @shiftedPath
def measurable_shiftedPath : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m), Adapted ℱ X →
    ∀ (τ : Ω → WithTop ℕ) (hτ : P207.IsDiscreteStoppingTime ℱ τ) (pInf : ℕ → S),
      Measurable[P207.terminalSigma ℱ] (shiftedPath X τ pInf)

def measurable_stoppedState : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m), Adapted ℱ X →
    ∀ (τ : Ω → WithTop ℕ) (hτ : P207.IsDiscreteStoppingTime ℱ τ) (iInf : S),
      Measurable[P207.stoppedSigma hτ] (stoppedState X τ iInf)

def shiftedPath_eq_on_finite : Prop :=
  ∀ {S : Type u} {Ω : Type v} (X : ℕ → Ω → S) (τ : Ω → WithTop ℕ)
    (p q : ℕ → S), Set.EqOn (shiftedPath X τ p) (shiftedPath X τ q) {ω | τ ω < ⊤}

def stoppedState_eq_on_finite : Prop :=
  ∀ {S : Type u} {Ω : Type v} (X : ℕ → Ω → S) (τ : Ω → WithTop ℕ)
    (i j : S), Set.EqOn (stoppedState X τ i) (stoppedState X τ j) {ω | τ ω < ⊤}

def strong_future_integral : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P ν X ℱ μ →
    ∀ (τ : Ω → WithTop ℕ) (hτ : P207.IsDiscreteStoppingTime ℱ τ)
      (pInf : ℕ → S) (iInf : S),
    ∀ (g : (ℕ → S) → ℝ), Measurable g → (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) →
    ∀ (A : Set Ω), MeasurableSet[P207.stoppedSigma hτ] A →
      (∫ ω in A ∩ {ω | τ ω < ⊤}, g (shiftedPath X τ pInf ω) ∂μ) =
        ∫ ω in A ∩ {ω | τ ω < ⊤}, stateExpectation P (stoppedState X τ iInf ω) g ∂μ

def strong_future_lintegral : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P ν X ℱ μ →
    ∀ (τ : Ω → WithTop ℕ) (hτ : P207.IsDiscreteStoppingTime ℱ τ)
      (pInf : ℕ → S) (iInf : S),
    ∀ (g : (ℕ → S) → ℝ≥0∞), Measurable g →
    ∀ (A : Set Ω), MeasurableSet[P207.stoppedSigma hτ] A →
      (∫⁻ ω in A ∩ {ω | τ ω < ⊤}, g (shiftedPath X τ pInf ω) ∂μ) =
        ∫⁻ ω in A ∩ {ω | τ ω < ⊤},
          ∫⁻ p, g p ∂statePathLaw P (stoppedState X τ iInf ω) ∂μ

def strong_future_condExp : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P ν X ℱ μ →
    ∀ (τ : Ω → WithTop ℕ) (hτ : P207.IsDiscreteStoppingTime ℱ τ)
      (pInf : ℕ → S) (iInf : S),
    (∀ᵐ ω ∂μ, τ ω < ⊤) →
    ∀ (g : (ℕ → S) → ℝ), Measurable g → (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) →
      μ[(fun ω => g (shiftedPath X τ pInf ω)) | P207.stoppedSigma hτ] =ᵐ[μ]
        fun ω => stateExpectation P (stoppedState X τ iInf ω) g

def strong_future_event_condExp : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P ν X ℱ μ →
    ∀ (τ : Ω → WithTop ℕ) (hτ : P207.IsDiscreteStoppingTime ℱ τ)
      (pInf : ℕ → S) (iInf : S),
    (∀ᵐ ω ∂μ, τ ω < ⊤) →
    ∀ (B : Set (ℕ → S)), MeasurableSet B →
      μ[(fun ω => B.indicator (fun _ => (1 : ℝ)) (shiftedPath X τ pInf ω)) |
        P207.stoppedSigma hτ] =ᵐ[μ]
        fun ω => (statePathLaw P (stoppedState X τ iInf ω) B).toReal

end StrongMarkovSpec
end
end P207.Markov
