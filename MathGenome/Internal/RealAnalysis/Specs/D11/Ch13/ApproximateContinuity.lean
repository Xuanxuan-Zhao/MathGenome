import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.AveragesMaximalDefinition

/-! Independent statements of paper.tex:4533–4542. The numerator is the
completed Lebesgue measure of the strict deviation set inside the centered
open ball. Both measures are finite on balls; `.toReal` therefore gives the
ordinary real density quotient for every positive radius. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Specs.D11.Ch13.ApproximateContinuity
open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch13.AveragesMaximalDefinition

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace_value n

/-- Every positive deviation threshold has density zero at a Lebesgue point
of the chosen finite-valued real or complex measurable representative. -/
def at_lebesguePoint : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (hf : locallyIntegrable_value f) (x : Point n),
    lebesguePoint_value f hf x → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun r : ℝ =>
        (lebesgue_value n {y | y ∈ Metric.ball x r ∧ ε < ‖f y - f x‖}).toReal /
          (lebesgue_value n (Metric.ball x r)).toReal)
        (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- One measurable null set works simultaneously for all positive deviation
thresholds, with no global integrability or finite-total-mass assumption. -/
def approximate_continuity_ae : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (_hf : locallyIntegrable_value f),
    ∃ N : Set (Point n), MeasurableSet N ∧ lebesgue_value n N = 0 ∧
      ∀ x ∉ N, ∀ ε : ℝ, 0 < ε →
        Tendsto (fun r : ℝ =>
          (lebesgue_value n {y | y ∈ Metric.ball x r ∧ ε < ‖f y - f x‖}).toReal /
            (lebesgue_value n (Metric.ball x r)).toReal)
          (𝓝[>] (0 : ℝ)) (𝓝 0)

end Specs.D11.Ch13.ApproximateContinuity
