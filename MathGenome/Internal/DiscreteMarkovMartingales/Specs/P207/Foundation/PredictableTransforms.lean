import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

/-- Increment over the interval from k to k+1. -/
def processIncrement {Ω : Type u} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  X (k + 1) ω - X k ω

/-- Gain at time n, with H_k measurable at time k when used predictably. -/
def predictableTransform {Ω : Type u} (H X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, H k ω * processIncrement X k ω

namespace PredictableTransformsSpec

def processIncrementType := {Ω : Type u} → (ℕ → Ω → ℝ) → ℕ → Ω → ℝ

def processIncrementValue : processIncrementType.{u} :=
  fun {_} X k ω => X (k + 1) ω - X k ω

def predictableTransformType :=
  {Ω : Type u} → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → ℕ → Ω → ℝ

def predictableTransformValue : predictableTransformType.{u} :=
  fun {_} H X n ω => ∑ k ∈ Finset.range n, H k ω * (X (k + 1) ω - X k ω)

def predictableTransform_zero : Prop :=
  ∀ {Ω : Type u} (H X : ℕ → Ω → ℝ) (ω : Ω),
    predictableTransform H X 0 ω = 0

def predictableTransform_succ : Prop :=
  ∀ {Ω : Type u} (H X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω),
    predictableTransform H X (n + 1) ω =
      predictableTransform H X n ω + H n ω * processIncrement X n ω

def processIncrement_predictableTransform : Prop :=
  ∀ {Ω : Type u} (H X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω),
    processIncrement (predictableTransform H X) n ω = H n ω * processIncrement X n ω

def adapted_predictableTransform : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ),
    Adapted ℱ H → Adapted ℱ X → Adapted ℱ (predictableTransform H X)

def integrable_predictableTransform : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) (H X : ℕ → Ω → ℝ),
    (∀ k, Integrable (fun ω => H k ω * processIncrement X k ω) μ) →
    ∀ n, Integrable (predictableTransform H X n) μ

def integrable_transform_products_of_bounded : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ),
    Adapted ℱ H → (∀ n, Integrable (X n) μ) →
    (∀ k, ∃ C : ℝ, ∀ ω, ‖H k ω‖ ≤ C) →
    ∀ k, Integrable (fun ω => H k ω * processIncrement X k ω) μ

def martingale_predictableTransform : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ),
    IsMartingale X ℱ μ → Adapted ℱ H →
    (∀ k, Integrable (fun ω => H k ω * processIncrement X k ω) μ) →
    IsMartingale (predictableTransform H X) ℱ μ

def submartingale_predictableTransform : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ),
    IsSubmartingale X ℱ μ → Adapted ℱ H → (∀ k ω, 0 ≤ H k ω) →
    (∀ k, Integrable (fun ω => H k ω * processIncrement X k ω) μ) →
    IsSubmartingale (predictableTransform H X) ℱ μ

def martingale_predictableTransform_of_bounded : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ),
    IsMartingale X ℱ μ → Adapted ℱ H →
    (∀ k, ∃ C : ℝ, ∀ ω, ‖H k ω‖ ≤ C) →
    IsMartingale (predictableTransform H X) ℱ μ

def submartingale_predictableTransform_of_bounded : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ),
    IsSubmartingale X ℱ μ → Adapted ℱ H → (∀ k ω, 0 ≤ H k ω) →
    (∀ k, ∃ C : ℝ, ∀ ω, ‖H k ω‖ ≤ C) →
    IsSubmartingale (predictableTransform H X) ℱ μ

end PredictableTransformsSpec
end P207
