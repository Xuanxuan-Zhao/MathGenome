import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Radius
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
K03.13.ratio_radius, paper.tex:1366–1374. Limits are taken in the
order topology of [0,∞], so they include ordinary finite limits and
divergence to +∞. The radius is the upstream reciprocal root limsup.
The eventual nonvanishing hypothesis leaves every finite prefix arbitrary.
In ENNReal, 0⁻¹ = ∞ and ∞⁻¹ = 0. No ratio limit is asserted to exist.
-/
namespace Specs.SingleVariableAnalysis.Ch13.RatioRadius
open Ch01.SequenceLimit Ch13.PowerSeries
open Filter
open scoped Topology ENNReal

def realRatioRadius : Prop :=
  ∀ (a : ℕ → ℝ) (ℓ : ℝ≥0∞),
    sequenceEventuallyValue (fun n => a n ≠ 0) →
    Tendsto (fun n => ENNReal.ofReal |a (n+1) / a n|) atTop (𝓝 ℓ) →
    realPowerSeriesRadiusValue a = ℓ⁻¹

def complexRatioRadius : Prop :=
  ∀ (a : ℕ → ℂ) (ℓ : ℝ≥0∞),
    sequenceEventuallyValue (fun n => a n ≠ 0) →
    Tendsto (fun n => ENNReal.ofReal ‖a (n+1) / a n‖) atTop (𝓝 ℓ) →
    complexPowerSeriesRadiusValue a = ℓ⁻¹

def realInverseRatioRadius : Prop :=
  ∀ (a : ℕ → ℝ) (r : ℝ≥0∞),
    sequenceEventuallyValue (fun n => a n ≠ 0) →
    Tendsto (fun n => ENNReal.ofReal |a n / a (n+1)|) atTop (𝓝 r) →
    realPowerSeriesRadiusValue a = r

def complexInverseRatioRadius : Prop :=
  ∀ (a : ℕ → ℂ) (r : ℝ≥0∞),
    sequenceEventuallyValue (fun n => a n ≠ 0) →
    Tendsto (fun n => ENNReal.ofReal ‖a n / a (n+1)‖) atTop (𝓝 r) →
    complexPowerSeriesRadiusValue a = r

end Specs.SingleVariableAnalysis.Ch13.RatioRadius
