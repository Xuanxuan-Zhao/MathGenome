import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import Mathlib.Topology.MetricSpace.Cauchy

/-! The full finite-p Vitali Cauchy criterion (paper.tex:5264–5278).
The given functions are measurable representatives of the ordinary a.e. Lp
classes. The three controls on the right are the shared literal predicates.
The exponent is real and at least one, hence finite; the measure is arbitrary.
In particular no sigma-finiteness, atomlessness or positive-mass assumption is
made, either on the space or on a spatial truncation.
-/
open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace Specs.D11.Ch17.VitaliLpCauchy
open Specs.D11.Ch17.UniformControls Specs.D11.Ch07.ConvergenceDefinitions

def vitali_lp_cauchy : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (hp : 1 ≤ p),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    ∀ (F : ℕ → Lp 𝕜 (ENNReal.ofReal p) μ) (G : ℕ → X → 𝕜),
      (∀ n, Measurable (G n)) → (∀ n, G n =ᵐ[μ] (F n)) →
      (CauchySeq F ↔ cauchyInMeasure_value μ G ∧
        lpUiSmall_value μ p G ∧ lpSpatialTails_value μ p G)

end Specs.D11.Ch17.VitaliLpCauchy
