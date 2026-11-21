import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.CompleteTargetProjection

/-!
Independent statements for `paper.tex` 7709–7752,
`fa2:p2:prehilbert-projection`. The convex-set assertions use the accepted
complete-target interface. The additional assertions specialize to a complete
scalar-linear subspace of an arbitrary inner-product space. In particular,
there is no `CompleteSpace E` or nonzero-subspace hypothesis.

The projector is the shared ambient-valued orthogonal projector. Its existence
instance is obtained from completeness of the subtype with its induced metric.
`IsTopCompl`, together with the explicit unique decomposition, expresses the
internal topological direct sum E = Y ⊕ Yᗮ.
-/

noncomputable section

namespace ExpandedFA.Hilbert.PreHilbertProjection.Spec
universe u v

def ExistsUniqueNearestPoint : Prop :=
  CompleteTargetProjection.Spec.ExistsUniqueNearestPoint.{u, v}

def MinimizerIffVariational : Prop :=
  CompleteTargetProjection.Spec.MinimizerIffVariational.{u, v}

def ConvexProjectionNonexpansive : Prop :=
  CompleteTargetProjection.Spec.ConvexProjectionNonexpansive.{u, v}

/-- Completeness of the subspace alone gives a topological direct sum and
unique coordinates in the original ambient space. -/
def CompleteSubspaceDecomposition : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (Y : Submodule 𝕜 E), IsComplete (Y : Set E) →
    Submodule.IsTopCompl Y Y.orthogonal ∧
      ∀ x : E, ∃! yz : Y × Y.orthogonal, (yz.1 : E) + (yz.2 : E) = x

/-- The shared projector is scalar-linear and bounded, has norm at most one,
is orthogonal, fixes Y, gives a nearest point, and is nonexpansive. -/
def CompleteSubspaceProjection : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (Y : Submodule 𝕜 E) (hc : IsComplete (Y : Set E)),
    letI : CompleteSpace Y := hc.completeSpace_coe
    let P : E →L[𝕜] E := Conventions.Spec.OrthogonalProjectionValue 𝕜 E Y
    ‖P‖ ≤ 1 ∧
      (∀ x : E, P x ∈ Y ∧ x - P x ∈ Y.orthogonal) ∧
      (∀ y ∈ Y, P y = y) ∧
      (∀ (x z : E), z ∈ Y → ‖x - P x‖ ≤ ‖x - z‖) ∧
      LipschitzWith 1 P

/-- The zero target is included, even if E itself is zero or incomplete. -/
def ZeroSubspaceProjection : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E],
    let P : E →L[𝕜] E :=
      Conventions.Spec.OrthogonalProjectionValue 𝕜 E (⊥ : Submodule 𝕜 E)
    P = 0 ∧ ‖P‖ = 0

end ExpandedFA.Hilbert.PreHilbertProjection.Spec
