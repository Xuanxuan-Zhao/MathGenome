import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.FirmProjectionAndOrbitGaps
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
The minimum-displacement theorem, paper.tex 13171–13243.
`setDistance` is the infimum of ‖b-a‖ for a ∈ C₁, b ∈ C₂, represented
as the distance of zero from the pointwise difference. `minimumVector` is
exactly the epsilon choice used by the shared convex projector at zero.
The theorem includes its nearest-point property, so no existence certificate
is assumed. The index n=0 denotes the paper's first even gap u₂-u₁.
-/
noncomputable section
open Filter
open scoped Pointwise
namespace ExpandedFA.Geometry.MinimumDisplacement.Spec
universe u v

def setDistance {H : Type v} [NormedAddCommGroup H] (C₁ C₂ : Set H) : ℝ :=
  Metric.infDist (0 : H) (C₂ - C₁)

def minimumVector {H : Type v} [NormedAddCommGroup H] (C₁ C₂ : Set H) : H :=
  Classical.epsilon fun p => p ∈ closure (C₂ - C₁) ∧
    ∀ w ∈ closure (C₂ - C₁), ‖(0 : H) - p‖ ≤ ‖(0 : H) - w‖

def MinimumDisplacement : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C₁ C₂ : Set H) (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hc₁ : IsClosed C₁) (hc₂ : IsClosed C₂)
    (hv₁ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₁)
    (hv₂ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₂),
    let p := minimumVector C₁ C₂
    let δ := setDistance C₁ C₂
    let P₁ := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₁ hne₁ hc₁ hv₁
    let P₂ := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₂ hne₂ hc₂ hv₂
    (p ∈ closure (C₂ - C₁) ∧ ∀ w ∈ closure (C₂ - C₁), ‖p‖ ≤ ‖w‖) ∧
      ‖p‖ = δ ∧ ∀ u : ℕ → H,
        FirmProjectionAndOrbitGaps.Spec.IsAlternatingOrbit P₁ P₂ u →
        Tendsto (fun n => ‖u (2*n+2) - u (2*n+1)‖) atTop (nhds δ) ∧
        Tendsto (fun n => u (2*n+2) - u (2*n+1)) atTop (nhds p)

end ExpandedFA.Geometry.MinimumDisplacement.Spec
