import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Independent statement of paper.tex:1949–1973. Norm means absolute value
over ℝ and modulus over ℂ. The nonnegative integrals are the shared simple
suprema, and scalar integrals require the shared integrability predicate.
The domain and measure are arbitrary, including empty and incomplete spaces.
Natural indices enumerate the paper's sequence starting at one. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch06.AbsoluteSeries
open ScalarIntegral
open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch04.AeCommonException

def absoluteSeriesSum_type :=
  ∀ {X : Type u} {𝕜 : Type} [RCLike 𝕜], (ℕ → X → 𝕜) → X → 𝕜

/-- The absolutely convergent sum, with value zero at every other point. -/
def absoluteSeriesSum_value : absoluteSeriesSum_type.{u} := fun F x => by
  classical
  exact if Summable (fun n => ‖F n x‖) then ∑' n, F n x else 0

def absolute_series_interchange : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ℕ → X → 𝕜),
    (∀ n, Measurable (F n)) →
    (∑' n, nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖F n x‖)) < ∞ →
    almostEverywhere_value μ (fun x => Summable (fun n => ‖F n x‖)) ∧
    Measurable (absoluteSeriesSum_value F) ∧
    (∃ (hF : ∀ n, scalarIntegrable_value μ (F n))
        (hf : scalarIntegrable_value μ (absoluteSeriesSum_value F)),
      (∀ N, scalarIntegrable_value μ (fun x => ∑ n ∈ Finset.range N, F n x)) ∧
      (∀ N, scalarIntegrable_value μ
        (fun x => ‖(∑ n ∈ Finset.range N, F n x) - absoluteSeriesSum_value F x‖)) ∧
      almostEverywhere_value μ (fun x => HasSum (fun n => F n x)
        (absoluteSeriesSum_value F x)) ∧
      Tendsto (fun N => nonnegativeIntegral_value μ
        (fun x => ENNReal.ofReal
          ‖(∑ n ∈ Finset.range N, F n x) - absoluteSeriesSum_value F x‖))
        atTop (𝓝 0) ∧
      Summable (fun n => ‖scalarIntegral_value μ (F n) (hF n)‖) ∧
      HasSum (fun n => scalarIntegral_value μ (F n) (hF n))
        (scalarIntegral_value μ (absoluteSeriesSum_value F) hf) ∧
      scalarIntegral_value μ (absoluteSeriesSum_value F) hf =
        ∑' n, scalarIntegral_value μ (F n) (hF n))

end Specs.D11.Ch06.AbsoluteSeries
