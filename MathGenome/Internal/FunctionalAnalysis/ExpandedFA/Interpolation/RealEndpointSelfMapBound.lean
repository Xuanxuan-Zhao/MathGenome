import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Interpolation.RealEndpointSelfMapBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachGeometry.EndpointInterpolation

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u

namespace ExpandedFA.Interpolation.RealEndpointSelfMapBound
open ExpandedFA.BanachGeometry.EndpointInterpolationSpec
open ExpandedFA.BanachGeometry.EndpointInterpolation
open RealEndpointSelfMapBoundSpec

/-- Compatibility identifies any supplied L∞ endpoint map with the restriction
provided by the endpoint bridge. Consequently its exact norm occurs in the bound. -/
theorem self_map_bound_of_interpolation (𝕜 : Type*) [RCLike 𝕜]
    (h : InterpolationFor.{u} 𝕜) : SelfMapBoundFor.{u} 𝕜 := by
  intro X _ μ _ T S hS p hp hpt _
  have hT : PreservesInfinity T := by
    intro f
    rw [← hS f]
    exact Lp.memLp (S f)
  obtain ⟨S₀, hS₀, hU⟩ := h μ T hT
  have heq : S₀ = S := by
    apply ContinuousLinearMap.ext
    intro f
    exact toL1_injective ∞ le_top ((hS₀ f).trans (hS f).symm)
  subst S₀
  exact hU p hp hpt

/-- M_p ≤ M₁^(1/p) M∞^(1/p') for the given compatible complex endpoint maps. -/
theorem complex_self_map_bound : ComplexSelfMapBound.{u} :=
  self_map_bound_of_interpolation ℂ complex_interpolation

/-- The same sharp estimate for real-linear maps. The upstream assembly uses
norm-preserving complexification only at L¹ and L∞. -/
theorem real_self_map_bound : RealSelfMapBound.{u} :=
  self_map_bound_of_interpolation ℝ
    (real_interpolation_of_complexification complexification_one complexification_top)

end ExpandedFA.Interpolation.RealEndpointSelfMapBound
