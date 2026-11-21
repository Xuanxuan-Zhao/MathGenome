import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UniformSmoothDuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.UniformConvexSmoothDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.UniformFrechetNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14MilmanPettis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Stability

/-! Assembly of the complete Uniform duality theorem. The duality and
uniform differentiability arguments hold without completeness; the Banach
hypothesis is needed only to pass reflexivity from the dual to the primal. -/
namespace ExpandedFA.P1.UniformSmoothDuality
universe u v

/-- Uniform convexity of a normed space is uniform smoothness of its dual. -/
theorem uniformlyConvex_iff_dual_uniformlySmooth : Spec.ConvexIffDualSmooth.{u,v} :=
  UniformConvexSmoothDuals.uniformlyConvex_iff_dual_uniformlySmooth

/-- Uniform smoothness of a normed space is uniform convexity of its dual. -/
theorem uniformlySmooth_iff_dual_uniformlyConvex : Spec.SmoothIffDualConvex.{u,v} :=
  UniformConvexSmoothDuals.uniformlySmooth_iff_dual_uniformlyConvex

/-- Uniform smoothness is uniform real Fréchet differentiability on the sphere. -/
theorem uniformlySmooth_iff_uniformlyFrechet : Spec.SmoothIffUniformFrechet.{u,v} :=
  UniformFrechetNorm.uniformlySmooth_iff_uniformlyFrechet

/-- Uniformly smooth Banach spaces are reflexive, including the zero space. -/
theorem uniformlySmooth_banach_reflexive : Spec.SmoothBanachReflexive.{u,v} := by
  intro 𝕜 E _ _ _ _ hs
  have hc := (uniformlySmooth_iff_dual_uniformlyConvex 𝕜 E).mp hs
  have hr := C14MilmanPettis.milman_pettis 𝕜 (E →L[𝕜] 𝕜) hc
  have hd := (C14Stability.reflexivity_stability 𝕜 E (⊥ : Submodule 𝕜 E)
    (by simpa using (isClosed_singleton : IsClosed ({0} : Set E)))).2
  exact hd.mpr hr

/-- The unique norming map is uniformly continuous for the two norm metrics. -/
theorem uniformly_continuous_norming_map : Spec.UniformlyContinuousNormingMap.{u,v} :=
  UniformFrechetNorm.uniformly_continuous_norming_map

end ExpandedFA.P1.UniformSmoothDuality
