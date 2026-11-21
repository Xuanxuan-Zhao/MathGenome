import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.BishopRestrictionIsometry

/-! Independent statement of Bishop restriction interpolation,
`paper.tex`, `fa2:p5:bishop-interpolation`.
The compact spaces and subsets may be empty. The annihilator condition
uses finite scalar Radon measures and their total variation, as in the
shared restriction interface. -/

namespace ExpandedFA.PartV.BishopInterpolationSpec

open Set
open BishopRestrictionIsometrySpec
universe u

/-- Restriction maps the open unit ball onto the open unit ball, and is
surjective on all continuous functions on the compact subset. -/
def Interpolation (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (Y : Submodule 𝕜 C(K, 𝕜)),
    IsClosed (Y : Set C(K, 𝕜)) → ∀ F : TopologicalSpace.Compacts K,
    AnnihilatorsVanish Y F →
      restriction Y F '' Metric.ball (0 : Y) 1 = Metric.ball (0 : C(F, 𝕜)) 1 ∧
      Function.Surjective (restriction Y F)

def RealInterpolation : Prop := Interpolation.{u} ℝ
def ComplexInterpolation : Prop := Interpolation.{u} ℂ

end ExpandedFA.PartV.BishopInterpolationSpec
