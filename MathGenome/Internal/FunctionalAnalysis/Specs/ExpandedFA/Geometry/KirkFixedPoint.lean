import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.NormalStructure
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Independent statements of paper.tex, fa2:p2:kirk-fixed-point.
Weak compactness is compactness in the scalar-linear weak topology.
Convexity and normal structure use the underlying real space. -/
namespace ExpandedFA.Geometry.KirkFixedPoint.Spec
universe u v

/-- Kirk's theorem, with no weak continuity hypothesis on the self-map. -/
def KirkFixedPoint : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ K : Set E, K.Nonempty → IsCompact (toWeakSpace 𝕜 E '' K) →
      Convex ℝ K → NormalStructure.Spec.NormalStructureValue K →
      ∀ T : K → K, LipschitzWith 1 T → ∃ x : K, T x = x

/-- Browder–Göhde–Kirk in real or complex uniformly convex Banach spaces. -/
def BrowderGohdeKirk : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E],
    ExpandedFA.P1.C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E →
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ K : Set E, K.Nonempty → IsClosed K → Bornology.IsBounded K →
      Convex ℝ K → ∀ T : K → K, LipschitzWith 1 T → ∃ x : K, T x = x

end ExpandedFA.Geometry.KirkFixedPoint.Spec
