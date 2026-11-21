import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions

/-! The subspace assertion of `fa2:p2:alternating-projections`, paper.tex 13118ff.
The sequence starts at an arbitrary vector and projects first onto M, then N.
Closedness supplies the native orthogonal projections; no angle, dimension,
separability, or nontriviality condition is imposed. -/

noncomputable section
namespace ExpandedFA.Geometry.AlternatingSubspaceProjections.Spec
universe u v

/-- Norm convergence of the entire alternating sequence to the projection
of its initial vector onto the intersection, over either scalar field. -/
def AlternatingSubspaceConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M N : Submodule 𝕜 H) (hM : IsClosed (M : Set H))
    (hN : IsClosed (N : Set H)),
    letI : CompleteSpace M := hM.completeSpace_coe
    letI : CompleteSpace N := hN.completeSpace_coe
    letI : CompleteSpace ↥(M ⊓ N) := (hM.inter hN).completeSpace_coe
    ∀ (x₀ : H) (x : ℕ → H), x 0 = x₀ →
      (∀ n, x (2 * n + 1) = M.starProjection (x (2 * n))) →
      (∀ n, x (2 * n + 2) = N.starProjection (x (2 * n + 1))) →
      Filter.Tendsto x Filter.atTop (nhds ((M ⊓ N).starProjection x₀))

end ExpandedFA.Geometry.AlternatingSubspaceProjections.Spec
