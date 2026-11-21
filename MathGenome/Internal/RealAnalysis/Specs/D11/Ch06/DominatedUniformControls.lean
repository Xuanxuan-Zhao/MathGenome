import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.AbsoluteContinuityTails
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException

/-! Independent statements for paper.tex:2071–2085 (D11.06.vitali_route).
The scalar field is real or complex. Measurability is on the given
sigma-algebra, and domination holds off a measurable null envelope separately
for each index. The positive measure is arbitrary, including zero measures
and empty spaces. Set integrals use the canonical nonnegative integral of
the indicator times the norm. Suprema are taken in ℝ≥0∞, so the estimates
do not use a totalized scalar integral or any Chapter 17 definition.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace Specs.D11.Ch06.DominatedUniformControls

open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch04.AeCommonException

/-- The dominated measurable functions have finite absolute integrals. -/
def dominated_integrable : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f : ℕ → X → 𝕜) (g : X → ℝ),
    (∀ n, Measurable (f n)) → scalarIntegrable_value μ g → (∀ x, 0 ≤ g x) →
    (∀ n, almostEverywhere_value μ (fun x => ‖f n x‖ ≤ g x)) →
      ∀ n, scalarIntegrable_value μ (f n)

/-- The first displayed supremum inequality, for every measurable E. -/
def uniform_set_bound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f : ℕ → X → 𝕜) (g : X → ℝ),
    (∀ n, Measurable (f n)) → scalarIntegrable_value μ g → (∀ x, 0 ≤ g x) →
    (∀ n, almostEverywhere_value μ (fun x => ‖f n x‖ ≤ g x)) →
      ∀ E : Set X, MeasurableSet E →
        (⨆ n, nonnegativeIntegral_value μ
          (E.indicator (fun x => ENNReal.ofReal ‖f n x‖))) ≤
        nonnegativeIntegral_value μ (E.indicator (fun x => ENNReal.ofReal (g x)))

/-- The second displayed supremum inequality, on the complement of A. -/
def uniform_compl_bound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f : ℕ → X → 𝕜) (g : X → ℝ),
    (∀ n, Measurable (f n)) → scalarIntegrable_value μ g → (∀ x, 0 ≤ g x) →
    (∀ n, almostEverywhere_value μ (fun x => ‖f n x‖ ≤ g x)) →
      ∀ A : Set X, MeasurableSet A →
        (⨆ n, nonnegativeIntegral_value μ
          (Aᶜ.indicator (fun x => ENNReal.ofReal ‖f n x‖))) ≤
        nonnegativeIntegral_value μ (Aᶜ.indicator (fun x => ENNReal.ofReal (g x)))

/-- One positive δ controls the supremum for every measurable small set. -/
def uniform_small_sets : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f : ℕ → X → 𝕜) (g : X → ℝ),
    (∀ n, Measurable (f n)) → scalarIntegrable_value μ g → (∀ x, 0 ≤ g x) →
    (∀ n, almostEverywhere_value μ (fun x => ‖f n x‖ ≤ g x)) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set X, MeasurableSet E → μ E < ENNReal.ofReal δ →
          (⨆ n, nonnegativeIntegral_value μ
            (E.indicator (fun x => ENNReal.ofReal ‖f n x‖))) < ENNReal.ofReal ε

/-- One measurable finite-mass A controls all spatial tails at once. -/
def uniform_finite_measure_tail : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f : ℕ → X → 𝕜) (g : X → ℝ),
    (∀ n, Measurable (f n)) → scalarIntegrable_value μ g → (∀ x, 0 ≤ g x) →
    (∀ n, almostEverywhere_value μ (fun x => ‖f n x‖ ≤ g x)) →
      ∀ ε : ℝ, 0 < ε → ∃ A : Set X, MeasurableSet A ∧ μ A < ∞ ∧
        (⨆ n, nonnegativeIntegral_value μ
          (Aᶜ.indicator (fun x => ENNReal.ofReal ‖f n x‖))) < ENNReal.ofReal ε

end Specs.D11.Ch06.DominatedUniformControls
