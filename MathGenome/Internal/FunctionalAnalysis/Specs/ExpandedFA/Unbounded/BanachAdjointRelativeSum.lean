import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjoint

/-! Exact-domain assertion of `fa2:p3:banach-adjoint-sum`, paper.tex:14341–14360.
All duals are continuous and scalar-linear. -/
namespace ExpandedFA.Unbounded.BanachAdjointRelativeSumSpec

open BanachAdjointSpec

def RelativeSum : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (A B : Operator 𝕜 X Y),
    A.IsClosed → B.IsClosed →
    Dense (A.domain : Set X) → Dense (B.domain : Set X) →
    ∀ (hD : A.domain ≤ B.domain)
      (hD' : (adjointValue A).domain ≤ (adjointValue B).domain)
      (k C k' C' : ℝ),
    0 ≤ k → k < 1 → 0 ≤ C → 0 ≤ k' → k' < 1 → 0 ≤ C' →
    (∀ x : A.domain, ‖B ⟨(x : X), hD x.property⟩‖ ≤ k * ‖A x‖ + C * ‖(x : X)‖) →
    (∀ q : (adjointValue A).domain,
      ‖adjointValue B ⟨(q : Y →L[𝕜] 𝕜), hD' q.property⟩‖ ≤
        k' * ‖adjointValue A q‖ + C' * ‖(q : Y →L[𝕜] 𝕜)‖) →
    (A + B).domain = A.domain ∧ (A + B).IsClosed ∧
      (adjointValue (A + B)).domain = (adjointValue A).domain ∧
      adjointValue (A + B) = adjointValue A + adjointValue B

end ExpandedFA.Unbounded.BanachAdjointRelativeSumSpec
