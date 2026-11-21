import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
The expansion stage of `fa2:p2:singular-system`, paper.tex 11362–11393.
All sums converge in the norm topology. Only the nonzero singular part is
indexed; empty and finite families are allowed, while neither ambient Hilbert
space is assumed separable. Ordering and zero padding of the scalar sequence
belong to the separately allocated singular approximation stage.
-/
noncomputable section
universe u v w
namespace ExpandedFA.CompactSpectral.SingularExpansion.Spec

/-- A singular system retains both full kernels in the original Hilbert spaces. -/
structure SingularSystem (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (T : H →L[𝕜] G) where
  Index : Type u
  countable : Countable Index
  sigma : Index → ℝ
  rightVector : Index → H
  leftVector : Index → G
  positive : ∀ j, 0 < sigma j
  right_orthonormal : Orthonormal 𝕜 rightVector
  left_orthonormal : Orthonormal 𝕜 leftVector
  map_right : ∀ j, T (rightVector j) = (sigma j : 𝕜) • leftVector j
  adjoint_left : ∀ j,
    ContinuousLinearMap.adjoint T (leftVector j) = (sigma j : 𝕜) • rightVector j
  right_closedSpan :
    (Submodule.span 𝕜 (Set.range rightVector)).topologicalClosure = T.ker.orthogonal
  right_complement : IsCompl T.ker
    (Submodule.span 𝕜 (Set.range rightVector)).topologicalClosure
  left_closedSpan :
    (Submodule.span 𝕜 (Set.range leftVector)).topologicalClosure =
      (ContinuousLinearMap.adjoint T).ker.orthogonal
  left_complement : IsCompl (ContinuousLinearMap.adjoint T).ker
    (Submodule.span 𝕜 (Set.range leftVector)).topologicalClosure
  expansion : ∀ x : H,
    HasSum (fun j => ((sigma j : 𝕜) * inner 𝕜 (rightVector j) x) • leftVector j) (T x)
  adjoint_expansion : ∀ y : G,
    HasSum (fun j => ((sigma j : 𝕜) * inner 𝕜 (leftVector j) y) • rightVector j)
      (ContinuousLinearMap.adjoint T y)
  finite_multiplicity : ∀ s : ℝ, 0 < s → {j | sigma j = s}.Finite
  finite_away : ∀ ε : ℝ, 0 < ε → {j | ε ≤ sigma j}.Finite
  finite_rank : FiniteDimensional 𝕜 T.range → Finite Index
  zero_empty : T = 0 → IsEmpty Index

/-- Existence under exactly compactness and Hilbert completeness. -/
def Existence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
      Nonempty (SingularSystem 𝕜 H K T)

end ExpandedFA.CompactSpectral.SingularExpansion.Spec
