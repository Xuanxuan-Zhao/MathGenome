import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Projection
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Independent statements for the firm estimate and orbit comparison at
paper.tex:13184–13206. Convexity is real convexity even over ℂ. The projector
is the accepted nearest-point map on the original Hilbert space.
No intersection, boundedness, or distance-attainment assumption is imposed.
-/

noncomputable section
open Filter

namespace ExpandedFA.Geometry.FirmProjectionAndOrbitGaps.Spec
universe u v

/-- Starting at index zero, apply P₁ on odd steps and P₂ on even steps. -/
def IsAlternatingOrbit {H : Type v} (P₁ P₂ : H → H) (u : ℕ → H) : Prop :=
  ∀ n, u (n + 1) = if n % 2 = 0 then P₁ (u n) else P₂ (u n)

def FirmProjectionEstimate : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C : Set H) (hne : C.Nonempty) (hc : IsClosed C)
    (hv : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C) (x y : H),
    let P := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C hne hc hv
    ‖P x - P y‖ ^ 2 + ‖(x - P x) - (y - P y)‖ ^ 2 ≤ ‖x - y‖ ^ 2

/-- The sum is the paper's sum over j = 1,...,N, written j = i+1.
The first bound includes the nonnegative terminal energy. -/
def AlternatingOrbitComparison : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C₁ C₂ : Set H) (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hc₁ : IsClosed C₁) (hc₂ : IsClosed C₂)
    (hv₁ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₁)
    (hv₂ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₂),
    let P₁ := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₁ hne₁ hc₁ hv₁
    let P₂ := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₂ hne₂ hc₂ hv₂
    ∀ (u v : ℕ → H), IsAlternatingOrbit P₁ P₂ u → IsAlternatingOrbit P₁ P₂ v →
      ∀ N : ℕ,
        (∑ j ∈ Finset.range N, ‖(u (j+1) - v (j+1)) - (u j - v j)‖ ^ 2) ≤
          ‖u 0 - v 0‖ ^ 2 - ‖u N - v N‖ ^ 2 ∧
        (∑ j ∈ Finset.range N, ‖(u (j+1) - v (j+1)) - (u j - v j)‖ ^ 2) ≤
          ‖u 0 - v 0‖ ^ 2

/-- Index n starts at zero, so the even gaps are at indices 2n+2 and 2n+1.
Convergence in H is convergence in its original norm topology. -/
def EvenGapDifferenceTendstoZero : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C₁ C₂ : Set H) (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hc₁ : IsClosed C₁) (hc₂ : IsClosed C₂)
    (hv₁ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₁)
    (hv₂ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₂),
    let P₁ := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₁ hne₁ hc₁ hv₁
    let P₂ := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₂ hne₂ hc₂ hv₂
    ∀ (u v : ℕ → H), IsAlternatingOrbit P₁ P₂ u → IsAlternatingOrbit P₁ P₂ v →
      Tendsto (fun n => (u (2*n+2) - u (2*n+1)) -
        (v (2*n+2) - v (2*n+1))) atTop (nhds 0)

end ExpandedFA.Geometry.FirmProjectionAndOrbitGaps.Spec
