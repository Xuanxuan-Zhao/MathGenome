import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.Probability.Martingale.Centering

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

/-- A normalized predictable decomposition. The sum identity is allowed to hold
almost surely at each time, as is the normalization; predictability uses actual
measurable representatives.
Integrability of the martingale component is included in `IsMartingale`. -/
def IsDoobDecomposition {Ω : Type u} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m) (μ : Measure Ω)
    (M A : ℕ → Ω → ℝ) : Prop :=
  (∀ n, X n =ᵐ[μ] M n + A n) ∧ IsMartingale M ℱ μ ∧
    (∀ n, Integrable (A n) μ) ∧ A 0 =ᵐ[μ] 0 ∧
    (∀ n, Measurable[ℱ n] (A (n + 1)))

namespace DoobDecompositionSpec

/-- The canonical sum of conditional increments gives the required decomposition. -/
def canonical : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    Adapted ℱ X → (∀ n, Integrable (X n) μ) →
    IsDoobDecomposition X ℱ μ (martingalePart X ℱ μ) (predictablePart X ℱ μ) ∧
      (∀ n ω, X n ω = martingalePart X ℱ μ n ω + predictablePart X ℱ μ n ω)

/-- Existence for every integrable real adapted process, including time zero. -/
def existence : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    Adapted ℱ X → (∀ n, Integrable (X n) μ) →
    ∃ M A, IsDoobDecomposition X ℱ μ M A ∧ A 0 = 0 ∧
      ∀ n ω, X n ω = M n ω + A n ω

/-- Uniqueness on one event of full measure, hence also at every time. -/
def uniqueness : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X M A M' A' : ℕ → Ω → ℝ),
    IsDoobDecomposition X ℱ μ M A → IsDoobDecomposition X ℱ μ M' A' →
    ∀ᵐ ω ∂μ, ∀ n, M n ω = M' n ω ∧ A n ω = A' n ω

/-- The equivalence holds for every normalized predictable decomposition. -/
def submartingale_iff : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X M A : ℕ → Ω → ℝ),
    Adapted ℱ X → (∀ n, Integrable (X n) μ) →
    IsDoobDecomposition X ℱ μ M A →
    (IsSubmartingale X ℱ μ ↔ ∀ᵐ ω ∂μ, Monotone (fun n => A n ω))

end DoobDecompositionSpec
end P207
