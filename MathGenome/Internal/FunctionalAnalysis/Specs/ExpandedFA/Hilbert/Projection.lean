import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Independent statements for `paper.tex` 7372–7382, `fa2:p2:projection`.
The scalar field is real or complex, with the shared conjugate-first inner
product and real convexity. The norm and topology are the original ones.
Closed sets in the complete ambient space are complete targets; the chosen
nearest-point map is the shared complete-target map specialized accordingly.
No nontriviality, separability, or finite-dimensionality is assumed.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.Projection.Spec
universe u v

/-- The closed-convex-set projector in the original Hilbert space. -/
def ConvexProjectionType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C : Set H), C.Nonempty → IsClosed C →
    Conventions.Spec.RealConvexValue 𝕜 H C → H → H

def ConvexProjectionValue : ConvexProjectionType.{u, v} :=
  fun 𝕜 H _ _ _ _ C hne hclosed hv =>
    CompleteTargetProjection.Spec.ConvexProjectionValue 𝕜 H C hne hclosed.isComplete hv

def ExistsUniqueNearestPoint : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C : Set H), C.Nonempty → IsClosed C →
    Conventions.Spec.RealConvexValue 𝕜 H C →
    ∀ x : H, ∃! p : H, p ∈ C ∧ ∀ z ∈ C, ‖x - p‖ ≤ ‖x - z‖

/-- The variational characterization holds even without ambient completeness. -/
def MinimizerIffVariational : Prop :=
  CompleteTargetProjection.Spec.MinimizerIffVariational.{u, v}

def ConvexProjectionSpec : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hv : Conventions.Spec.RealConvexValue 𝕜 H C) (x : H),
    ConvexProjectionValue 𝕜 H C hne hclosed hv x ∈ C ∧
      ∀ z ∈ C, ‖x - ConvexProjectionValue 𝕜 H C hne hclosed hv x‖ ≤ ‖x - z‖

def EqConvexProjectionIffVariational : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hv : Conventions.Spec.RealConvexValue 𝕜 H C) (x p : H),
    p = ConvexProjectionValue 𝕜 H C hne hclosed hv x ↔
      p ∈ C ∧ ∀ z ∈ C, RCLike.re ⟪x - p, z - p⟫_𝕜 ≤ 0

def ConvexProjectionNonexpansive : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hv : Conventions.Spec.RealConvexValue 𝕜 H C) (x y : H),
    let P := ConvexProjectionValue 𝕜 H C hne hclosed hv
    ‖P x - P y‖ ≤ ‖x - y‖

/-- A topological internal direct sum, with unique orthogonal coordinates. -/
def ClosedSubspaceDecomposition : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : Submodule 𝕜 H), IsClosed (M : Set H) →
    Submodule.IsTopCompl M M.orthogonal ∧
      ∀ x : H, ∃! yz : M × M.orthogonal, (yz.1 : H) + (yz.2 : H) = x

/-- The shared orthogonal projector is linear, self-adjoint, contractive,
and idempotent, and supplies the orthogonal decomposition. -/
def ClosedSubspaceProjection : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)),
    letI : CompleteSpace M := hM.completeSpace_coe
    let P : H →L[𝕜] H := Conventions.Spec.OrthogonalProjectionValue 𝕜 H M
    (∀ (c : 𝕜) (x y : H), P (c • x + y) = c • P x + P y) ∧
      IsSelfAdjoint P ∧
      (∀ x y : H, ⟪P x, y⟫_𝕜 = ⟪x, P y⟫_𝕜) ∧
      ‖P‖ ≤ 1 ∧
      (∀ x : H, ‖P x‖ ≤ ‖x‖) ∧
      (∀ x : H, P x ∈ M ∧ x - P x ∈ M.orthogonal) ∧
      P.comp P = P

/-- The bounded scalar-linear projector is the same nearest-point map as
for convex sets. Real convexity of M comes from restriction of scalars. -/
def OrthogonalProjectionEqConvexProjection : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)),
    letI : CompleteSpace M := hM.completeSpace_coe
    letI := Conventions.Spec.RealificationValue 𝕜 H
    ∀ x : H, Conventions.Spec.OrthogonalProjectionValue 𝕜 H M x =
      ConvexProjectionValue 𝕜 H (M : Set H) ⟨0, M.zero_mem⟩ hM
        (M.restrictScalars ℝ).convex x

/-- L is arbitrary: closedness is required only of its topological closure. -/
def DoubleOrthogonalEqClosure : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : Submodule 𝕜 H), L.orthogonal.orthogonal = L.topologicalClosure

end ExpandedFA.Hilbert.Projection.Spec
