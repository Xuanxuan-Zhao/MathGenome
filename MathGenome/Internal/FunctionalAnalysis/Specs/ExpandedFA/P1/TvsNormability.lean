import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Gauge
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! Independent statements for the normability clause of
`fa2:p1:tvs-metrization`, paper.tex:1848–1893.

A norm is represented by a scalar seminorm together with positive
definiteness. `WithSeminorms` for its singleton family says exactly that
its norm topology is the given topology. In particular this formulation
does not use Mathlib's nonseparated notion of seminormability as a
substitute for a genuine norm. Real scalar restriction is compatible
with the original real or complex action.
-/

open Set Filter
open scoped Topology

namespace ExpandedFA.P1.TvsNormabilitySpec

/-- A Hausdorff real or complex LCS admits a compatible genuine norm
exactly when it has a bounded zero neighborhood. -/
def Normability : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [T2Space E],
    LCS 𝕜 E →
    ((∃ p : Seminorm 𝕜 E, (∀ x, p x = 0 ↔ x = 0) ∧
        WithSeminorms (fun _ : Unit => p)) ↔
      ∃ U ∈ 𝓝 (0 : E), Bounded U)

/-- Every bounded zero neighborhood contains an open absolutely convex
bounded zero neighborhood whose actual Minkowski gauge is a compatible
norm. Absolute convexity means balance over the original field and real
convexity. The gauge is the source's infimum over positive real dilations. -/
def GaugeNorm : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [T2Space E],
    LCS 𝕜 E → ∀ U ∈ 𝓝 (0 : E), Bounded U →
      ∃ V ∈ 𝓝 (0 : E), IsOpen V ∧ Balanced 𝕜 V ∧ Convex ℝ V ∧
        V ⊆ U ∧ Bounded V ∧
        ∃ p : Seminorm 𝕜 E,
          (∀ x, p x = C06GaugeSpec.gaugeValue V x) ∧
          Continuous (p : E → ℝ) ∧ (∀ x, p x = 0 ↔ x = 0) ∧
          WithSeminorms (fun _ : Unit => p)

end ExpandedFA.P1.TvsNormabilitySpec
