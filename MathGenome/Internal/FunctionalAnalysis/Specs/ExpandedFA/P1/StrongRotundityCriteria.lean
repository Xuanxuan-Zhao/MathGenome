import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.RotundDefinitions
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Cauchy

/-! The three criteria in paper.tex:4865–4899. The slice condition uses the
actual right-hand limit of the diameter as δ decreases to zero.
Convexity is real convexity in the canonically restricted scalar structure.
Neither completeness, closedness, nor nontriviality is required. -/
namespace ExpandedFA.P1.StrongRotundityCriteria.Spec
universe u v
open Filter
open scoped Topology
noncomputable section
variable (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The slice of the closed unit ball cut out by the scalar-linear dual. -/
def slice (f : E →L[𝕜] 𝕜) (δ : ℝ) : Set E :=
  {x | ‖x‖ ≤ 1 ∧ 1 - δ < RCLike.re (f x)}

/-- A useful ε–δ formulation, proved equivalent to the diameter limit. -/
def SmallSliceDiameters : Prop :=
  ∀ f : E →L[𝕜] 𝕜, ‖f‖ = 1 →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ Metric.diam (slice 𝕜 E f δ) < ε

/-- The manuscript's diameter limit, with δ tending to zero from above. -/
def ShrinkingSlices : Prop :=
  ∀ f : E →L[𝕜] 𝕜, ‖f‖ = 1 →
    Tendsto (fun δ : ℝ => Metric.diam (slice 𝕜 E f δ)) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Every unit sequence maximizing one fixed norm-one functional is Cauchy. -/
def UnitMaximizersCauchy : Prop :=
  ∀ (f : E →L[𝕜] 𝕜), ‖f‖ = 1 → ∀ x : ℕ → E,
    (∀ n, ‖x n‖ = 1) →
    Tendsto (fun n => RCLike.re (f (x n))) atTop (𝓝 1) → CauchySeq x

/-- Every minimizing sequence, at each point and in each nonempty convex set.
The sequence belongs to the actual set; the set need not be closed. -/
def MinimizersCauchy : Prop :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  ∀ (C : Set E), C.Nonempty → Convex ℝ C → ∀ (p : E) (x : ℕ → E),
    (∀ n, x n ∈ C) →
    Tendsto (fun n => dist (x n) p) atTop (𝓝 (Metric.infDist p C)) → CauchySeq x

def Equivalence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (ShrinkingSlices 𝕜 E ↔ UnitMaximizersCauchy 𝕜 E) ∧
    (UnitMaximizersCauchy 𝕜 E ↔ MinimizersCauchy 𝕜 E)

end
end ExpandedFA.P1.StrongRotundityCriteria.Spec
