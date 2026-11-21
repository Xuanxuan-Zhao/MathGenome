import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped MeasureTheory
universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- Finite cutoff definition; infinity is allowed. -/
def IsDiscreteStoppingTime (ℱ : Filtration ℕ m) (τ : Ω → WithTop ℕ) : Prop :=
  ∀ n : ℕ, MeasurableSet[ℱ n] {ω | τ ω ≤ n}

/-- The source's stopped sigma-algebra, including terminal measurability. -/
@[instance_reducible] def stoppedSigma {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) : MeasurableSpace Ω :=
  MeasureTheory.IsStoppingTime.measurableSpace hτ

/-- The minimum with finite time is always finite. -/
noncomputable def stoppedProcess (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) : ℕ → Ω → ℝ :=
  fun n ω => X (min (n : WithTop ℕ) (τ ω)).untopA ω

/-- A full-space stopped value with an explicit value on the infinite layer. -/
noncomputable def fullStoppedValue (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => if τ ω = ⊤ then Y ω else X (τ ω).untopA ω

namespace StoppingSpec

def IsDiscreteStoppingTimeType :=
  {Ω : Type u} → [m : MeasurableSpace Ω] → Filtration ℕ m → (Ω → WithTop ℕ) → Prop

noncomputable def IsDiscreteStoppingTimeValue : IsDiscreteStoppingTimeType.{u} :=
  fun {_} [_] ℱ τ => ∀ n : ℕ, MeasurableSet[ℱ n] {ω | τ ω ≤ n}

def stoppedSigmaType :=
  {Ω : Type u} → [m : MeasurableSpace Ω] → {ℱ : Filtration ℕ m} → {τ : Ω → WithTop ℕ} → IsDiscreteStoppingTime ℱ τ → MeasurableSpace Ω

noncomputable def stoppedSigmaValue : stoppedSigmaType.{u} :=
  fun {_} [_] {_} {_} hτ => MeasureTheory.IsStoppingTime.measurableSpace hτ

def stoppedProcessType :=
  {Ω : Type u} → (ℕ → Ω → ℝ) → (Ω → WithTop ℕ) → ℕ → Ω → ℝ

noncomputable def stoppedProcessValue : stoppedProcessType.{u} :=
  fun {_} X τ n ω => X (min (n : WithTop ℕ) (τ ω)).untopA ω

def fullStoppedValueType :=
  {Ω : Type u} → (ℕ → Ω → ℝ) → (Ω → WithTop ℕ) → (Ω → ℝ) → Ω → ℝ

noncomputable def fullStoppedValueValue : fullStoppedValueType.{u} :=
  fun {_} X τ Y ω => if τ ω = ⊤ then Y ω else X (τ ω).untopA ω

def isDiscreteStoppingTime_iff : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ (ℱ : Filtration ℕ m) (τ : Ω → WithTop ℕ),
    IsDiscreteStoppingTime ℱ τ ↔ ∀ n : ℕ, MeasurableSet[ℱ n] {ω | τ ω ≤ n}

def stoppedSigma_membership : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (A : Set Ω),
    MeasurableSet[stoppedSigma hτ] A ↔
      MeasurableSet[terminalSigma ℱ] A ∧
        ∀ n : ℕ, MeasurableSet[ℱ n] (A ∩ {ω | τ ω ≤ n})

def stopping_layer_measurable : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (n : ℕ),
    MeasurableSet[ℱ n] {ω | τ ω = n}

def stopping_layer_stopped_measurable : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (n : ℕ),
    MeasurableSet[stoppedSigma hτ] {ω | τ ω = n}

def stoppedSigma_layers : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (A : Set Ω),
    MeasurableSet[stoppedSigma hτ] A ↔
      MeasurableSet[terminalSigma ℱ] A ∧
        ∀ n : ℕ, MeasurableSet[ℱ n] (A ∩ {ω | τ ω = n})

def stopping_finite_measurable : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ),
    MeasurableSet[stoppedSigma hτ] {ω | τ ω < ⊤}

def stoppedSigma_mono : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {σ τ : Ω → WithTop ℕ}
    (hσ : IsDiscreteStoppingTime ℱ σ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (hle : ∀ ω, σ ω ≤ τ ω),
    stoppedSigma hσ ≤ stoppedSigma hτ

def stoppedSigma_const : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ (ℱ : Filtration ℕ m) (n : ℕ),
    stoppedSigma (MeasureTheory.isStoppingTime_const ℱ n) = ℱ n

def stoppedSigma_le_terminal : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ),
    stoppedSigma hτ ≤ terminalSigma ℱ

def stoppedProcess_min_finite : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ (τ : Ω → WithTop ℕ) (n : ℕ) (ω : Ω),
    min (n : WithTop ℕ) (τ ω) ≠ ⊤

def stoppedProcess_at_top : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (n : ℕ) (ω : Ω) (h : τ ω = ⊤),
    stoppedProcess X τ n ω = X n ω

def stoppedProcess_at_finite : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (n k : ℕ) (ω : Ω) (h : τ ω = k),
    stoppedProcess X τ n ω = X (min n k) ω

def fullStoppedValue_at_top : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (Y : Ω → ℝ) (ω : Ω) (h : τ ω = ⊤),
    fullStoppedValue X τ Y ω = Y ω

def fullStoppedValue_at_finite : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (Y : Ω → ℝ) (n : ℕ) (ω : Ω) (h : τ ω = n),
    fullStoppedValue X τ Y ω = X n ω

def adapted_stoppedProcess : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (X : ℕ → Ω → ℝ) (hX : Adapted ℱ X),
    Adapted ℱ (stoppedProcess X τ)

def integrable_stoppedProcess : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (X : ℕ → Ω → ℝ) (μ : Measure Ω)
    (hX : ∀ k, Integrable (X k) μ) (n : ℕ),
    Integrable (stoppedProcess X τ n) μ

def measurable_fullStoppedValue : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (X : ℕ → Ω → ℝ) (hX : Adapted ℱ X)
    (Y : Ω → ℝ) (hY : Measurable[terminalSigma ℱ] Y),
    Measurable[stoppedSigma hτ] (fullStoppedValue X τ Y)

def integrable_fullStoppedValue_bounded : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω],
  ∀ {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (μ : Measure Ω) (hX : ∀ k, Integrable (X k) μ)
    (N : ℕ) (hbound : ∀ ω, τ ω ≤ N),
    Integrable (fullStoppedValue X τ Y) μ

end StoppingSpec
end P207
