import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent specification for paper.tex:3501–3521.
`ℝ≥0∞` retains infinite level measures and infinite integrals. The right-hand
integral is over positive real thresholds against one-dimensional Lebesgue
measure. The canonical nonnegative integral is the upstream simple-minorant
integral. A normed scalar field `RCLike` covers both real and complex scalars.
No completeness or size assumption is imposed on the measure on X.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace Specs.D11.Ch10.DistributionLayerCake

def distribution_type :=
  ∀ {X : Type u} {K : Type v} [MeasurableSpace X] [Norm K],
    Measure X → (X → K) → ℝ → ℝ≥0∞

/-- Defined on all real thresholds; the source uses its restriction to t > 0. -/
def distribution_value : distribution_type.{u,v} :=
  fun μ f t => μ {x | t < ‖f x‖}

def decreasing : Prop :=
  ∀ {X : Type u} {K : Type v} [MeasurableSpace X] [RCLike K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure X) (f : X → K),
    Measurable f → Antitone (distribution_value μ f)

/-- Right continuity in the extended nonnegative real topology, including ∞. -/
def right_continuous : Prop :=
  ∀ {X : Type u} {K : Type v} [MeasurableSpace X] [RCLike K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure X) (f : X → K),
    Measurable f → ∀ t : ℝ, 0 < t →
    ContinuousWithinAt (distribution_value μ f) (Ici t) t

def layer_cake : Prop :=
  ∀ {X : Type u} {K : Type v} [MeasurableSpace X] [RCLike K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure X) (f : X → K),
    Measurable f → ∀ p : ℝ, 0 < p →
    Ch05.NonnegativeIntegral.nonnegativeIntegral_value μ
      (fun x => ENNReal.ofReal (‖f x‖ ^ p)) =
    ENNReal.ofReal p *
      Ch05.NonnegativeIntegral.nonnegativeIntegral_value
        ((volume : Measure ℝ).restrict (Ioi 0))
        (fun t => ENNReal.ofReal (t ^ (p - 1)) * distribution_value μ f t)

end Specs.D11.Ch10.DistributionLayerCake
