import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Differential.Definitions
import Mathlib.Analysis.Convex.Segment

/-!
Independent statements for paper.tex:6738–6753 (`fa2:p1:banach-chain-rule`).
Functions on open domains are represented by ambient functions restricted to
those domains, as in the upstream derivative interface. The derivative is the
native `fderivWithin`, so no new derivative notion or assumed certificate occurs.
The segment in the second statement uses the underlying real vector space,
also when the scalar field is complex. No continuity of the derivative is required.
-/

namespace ExpandedFA.Differential.Spec

/-- The composition has the composed derivative, which is also its canonical
derivative on the open domain. Differentiability is needed only at the two
displayed points; no global regularity is imposed on either function. -/
def ChainRule : Prop :=
  ∀ (𝕜 E F G : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    (Ω : Set E) (Λ : Set F), IsOpen Ω → IsOpen Λ →
    ∀ (f : E → F) (g : F → G) (x : E), x ∈ Ω → f x ∈ Λ →
      DifferentiableWithinAt 𝕜 f Ω x → DifferentiableWithinAt 𝕜 g Λ (f x) →
      HasFDerivWithinAt (g ∘ f)
        ((fderivWithin 𝕜 g Λ (f x)).comp (fderivWithin 𝕜 f Ω x)) Ω x ∧
      fderivWithin 𝕜 (g ∘ f) Ω x =
        (fderivWithin 𝕜 g Λ (f x)).comp (fderivWithin 𝕜 f Ω x)

/-- A bound on the operator norm of the derivative at every point of the
contained segment bounds the increment. The pointwise bound expresses the
printed supremum bound without requiring a separately chosen supremum.
Endpoints, the constant segment, and both scalar fields are included. -/
def MeanValueEstimate : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (Ω : Set E), IsOpen Ω → ∀ (f : E → F) (x y : E) (M : ℝ),
      segment ℝ x y ⊆ Ω →
      (∀ z ∈ segment ℝ x y, DifferentiableWithinAt 𝕜 f Ω z) →
      (∀ z ∈ segment ℝ x y, ‖fderivWithin 𝕜 f Ω z‖ ≤ M) →
      ‖f y - f x‖ ≤ M * ‖y - x‖

end ExpandedFA.Differential.Spec
