import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.SingularExpansion

/-! Picard criterion, `fa2:p5:picard`, paper.tex 21856–21886.
Only positive singular vectors are indexed. Finite and empty families are
included; both ambient kernels are unrestricted. Scalar products are
conjugate-first, and every vector series converges in norm.
The separately allocated PicardInstability goal covers instability.
-/
noncomputable section
universe u v w z
namespace ExpandedFA.PartV.Picard.Spec

variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]

/-- Full characterization of the distinguished solution, including strict
minimality and the whole affine fiber. -/
def SolutionProperties (K : H →L[𝕜] G) (f : G) (d : H) : Prop :=
  K d = f ∧ d ∈ K.ker.orthogonal ∧
  (∀ u, K u = f → u ∈ K.ker.orthogonal → u = d) ∧
  (∀ u, K u = f ↔ ∃ z ∈ K.ker, u = d + z) ∧
  (∀ u, K u = f → ‖d‖ ≤ ‖u‖ ∧ (‖u‖ = ‖d‖ ↔ u = d)) ∧
  (∀ z ∈ K.ker, ‖d + z‖ ^ 2 = ‖d‖ ^ 2 + ‖z‖ ^ 2)

/-- The rectangular criterion for any of the proved compact singular systems. -/
def SingularCriterion : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (K : H →L[𝕜] G)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem 𝕜 H G K) (f : G),
    (∃ u, K u = f) ↔
      f ∈ (ContinuousLinearMap.adjoint K).ker.orthogonal ∧
      Summable (fun j => ‖inner 𝕜 (S.leftVector j) f‖ ^ 2 / S.sigma j ^ 2)

/-- Norm convergence and all uniqueness/minimum-norm conclusions under the
exact two Picard conditions. The proved singular system is supplied as data;
no assumption about closed range is imposed. -/
def SingularSolution : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (K : H →L[𝕜] G)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem 𝕜 H G K) (f : G),
    f ∈ (ContinuousLinearMap.adjoint K).ker.orthogonal →
    Summable (fun j => ‖inner 𝕜 (S.leftVector j) f‖ ^ 2 / S.sigma j ^ 2) →
    let terms := fun j => ((S.sigma j : 𝕜)⁻¹ * inner 𝕜 (S.leftVector j) f) • S.rightVector j
    HasSum terms (∑' j, terms j) ∧ SolutionProperties K f (∑' j, terms j)


/-- With no singular vectors, compatibility forces the datum to be zero. -/
def EmptyCompatibility : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (K : H →L[𝕜] G)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem 𝕜 H G K) [IsEmpty S.Index] (f : G),
    f ∈ (ContinuousLinearMap.adjoint K).ker.orthogonal ↔ f = 0


end ExpandedFA.PartV.Picard.Spec
