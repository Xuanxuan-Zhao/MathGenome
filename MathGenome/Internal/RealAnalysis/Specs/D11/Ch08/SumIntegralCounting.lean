import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.AtomicIntegrals
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.AbsoluteSeries

/-!
Independent statements for paper.tex:2880–2896, counting-factor interchange.
The measure on X is arbitrary; no finiteness or completeness is assumed.
Nonnegative integrals are the shared simple-minorant suprema. Scalar
integrals require actual measurability and finite absolute integral, for
both real and complex scalars. The sum is the shared absolutely convergent
sum, reset to zero elsewhere. Natural indices enumerate the source sequence.
The final statement expresses the nonnegative identity as iterated integrals
against counting measure on the full power-set sigma-algebra of ℕ.
-/

open MeasureTheory
open scoped ENNReal

universe u
noncomputable section

namespace Specs.D11.Ch08.SumIntegralCounting

open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch06.AbsoluteSeries
open Specs.D11.Ch04.AeCommonException

def nonnegative_interchange : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞), (∀ n, Measurable (f n)) →
    nonnegativeIntegral_value μ (fun x => ∑' n, f n x) =
      ∑' n, nonnegativeIntegral_value μ (f n)

def scalar_interchange : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : ℕ → X → 𝕜),
    (∀ n, Measurable (f n)) →
    (∑' n, nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f n x‖)) < ∞ →
    almostEverywhere_value μ (fun x => Summable (fun n => ‖f n x‖)) ∧
    Measurable (absoluteSeriesSum_value f) ∧
    (∃ (hF : ∀ n, scalarIntegrable_value μ (f n))
        (hs : scalarIntegrable_value μ (absoluteSeriesSum_value f)),
      almostEverywhere_value μ (fun x => HasSum (fun n => f n x)
        (absoluteSeriesSum_value f x)) ∧
      Summable (fun n => ‖scalarIntegral_value μ (f n) (hF n)‖) ∧
      HasSum (fun n => scalarIntegral_value μ (f n) (hF n))
        (scalarIntegral_value μ (absoluteSeriesSum_value f) hs) ∧
      scalarIntegral_value μ (absoluteSeriesSum_value f) hs =
        ∑' n, scalarIntegral_value μ (f n) (hF n))

def nonnegative_counting_interchange : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞), (∀ n, Measurable (f n)) →
    letI : MeasurableSpace ℕ := ⊤
    nonnegativeIntegral_value μ (fun x =>
      nonnegativeIntegral_value (Measure.count : Measure ℕ) (fun n => f n x)) =
    nonnegativeIntegral_value (Measure.count : Measure ℕ)
      (fun n => nonnegativeIntegral_value μ (f n))

end Specs.D11.Ch08.SumIntegralCounting
