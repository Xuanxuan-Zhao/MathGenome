import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.EssentialBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.RCLike.Basic

/-! The two endpoint counterexamples in paper.tex:3827–3842.
The measure is the ordinary completion of real Borel Lebesgue measure.
`ContinuousOn g (Icc (α := ℝ) 0 1)` represents a continuous real function on the
closed interval: values outside the interval are arbitrary and are ignored
by the restricted measure. Any function on the interval has such an ambient
representative, by extending it arbitrarily outside. The norm is the shared
ordinary a.e. essential norm, with extended nonnegative values. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch11.InfinityDensityFailure
open Specs.D11.Ch04.EssentialBounds

def continuous_approximation_lower_bound : Prop :=
  ∀ g : ℝ → ℝ, ContinuousOn g (Icc (α := ℝ) 0 1) →
    (1 / 2 : ℝ≥0∞) ≤ essentialSupNorm_value
      ((volume : Measure ℝ).completion.restrict (Icc (α := ℝ) (0 : ℝ) 1))
      (fun x : ℝ => (Icc (α := ℝ) (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x - g x)

def translated_indicator_norm : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (h : ℝ), 0 < |h| → |h| < 1 →
    essentialSupNorm_value (volume : Measure ℝ).completion
      (fun x : ℝ => (Icc (α := ℝ) (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜)) (x - h) -
        (Icc (α := ℝ) (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜)) x) = 1

end Specs.D11.Ch11.InfinityDensityFailure
