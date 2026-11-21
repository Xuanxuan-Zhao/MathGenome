import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.GreedyUpcrossings

/-! Full finite-horizon statement of `paper.tex`, Theorem `p207:upcross`.
The canonical count includes sales at time `n`, and times begin at zero.
Measurability is asserted in the time-`n` sigma-algebra. -/
open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207.UpcrossingInequalitySpec

def measurable_count : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m)
    (X : ℕ → Ω → ℝ), Adapted ℱ X → ∀ (a b : ℝ), a < b → ∀ n,
    Measurable[ℱ n] (fun ω => greedyUpcrossings (fun k => X k ω) a b n)

def integrable_count : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ), Adapted ℱ X →
    ∀ (a b : ℝ), a < b → ∀ n,
    Integrable (fun ω => (greedyUpcrossings (fun k => X k ω) a b n : ℝ)) μ

/-- The sharper estimate and its comparison with the original weaker bound. -/
def inequality : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ), IsSubmartingale X ℱ μ →
    ∀ (a b : ℝ), a < b → ∀ n,
    (b - a) * (∫ ω, (greedyUpcrossings (fun k => X k ω) a b n : ℝ) ∂μ) ≤
      (∫ ω, (X n ω - a)⁺ ∂μ) - (∫ ω, (X 0 ω - a)⁺ ∂μ) ∧
    (∫ ω, (X n ω - a)⁺ ∂μ) - (∫ ω, (X 0 ω - a)⁺ ∂μ) ≤
      (∫ ω, (X n ω - a)⁺ ∂μ) + (∫ ω, (X 0 ω - a)⁻ ∂μ)

def weaker_inequality : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ), IsSubmartingale X ℱ μ →
    ∀ (a b : ℝ), a < b → ∀ n,
    (b - a) * (∫ ω, (greedyUpcrossings (fun k => X k ω) a b n : ℝ) ∂μ) ≤
      (∫ ω, (X n ω - a)⁺ ∂μ) + (∫ ω, (X 0 ω - a)⁻ ∂μ)

end P207.UpcrossingInequalitySpec
