import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.RieszRepresentation
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Projection

/-!
Independent statements for `paper.tex` 7499–7512, `fa2:p2:adjoint`.
All spaces are real or complex Hilbert spaces with the original norm and
conjugate-first inner product. The adjoint acts K → H, whereas the Banach
transpose acts on scalar-linear continuous duals by precomposition. The final
Riesz identity explicitly relates these two different constructions.

Invariance means T(M) ⊆ M. Reduction means invariance of both M and Mᗮ.
Projection formulas use the shared ambient-valued orthogonal projector.
There are no dimension, separability, nonzero-space, or closed-range assumptions.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.Adjoint.Spec
universe u v w z

/-- The canonical bounded Hilbert adjoint on every bounded H → K. -/
def AdjointType :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], (H →L[𝕜] K) → (K →L[𝕜] H)

def AdjointValue : AdjointType.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ _ T => ContinuousLinearMap.adjoint T

def InvariantSubspaceType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H],
    Submodule 𝕜 H → (H →L[𝕜] H) → Prop

def InvariantSubspaceValue : InvariantSubspaceType.{u, v} :=
  fun _ _ _ _ _ M T => ∀ x ∈ M, T x ∈ M

def ReducingSubspaceType := InvariantSubspaceType.{u, v}

def ReducingSubspaceValue : ReducingSubspaceType.{u, v} :=
  fun 𝕜 H _ _ _ M T =>
    InvariantSubspaceValue 𝕜 H M T ∧ InvariantSubspaceValue 𝕜 H M.orthogonal T

def DefiningIdentity : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K) (x : H) (y : K),
    ⟪T x, y⟫_𝕜 = ⟪x, AdjointValue 𝕜 H K T y⟫_𝕜

def ExistenceUniqueness : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K),
    ∃! S : K →L[𝕜] H, ∀ (x : H) (y : K), ⟪T x, y⟫_𝕜 = ⟪x, S y⟫_𝕜

def NormEquality : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K), ‖T‖ = ‖AdjointValue 𝕜 H K T‖

def CstarNorm : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K), ‖(AdjointValue 𝕜 H K T).comp T‖ = ‖T‖ ^ 2

def Involution : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K), AdjointValue 𝕜 K H (AdjointValue 𝕜 H K T) = T

def Composition : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) (L : Type z) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K] [NormedAddCommGroup L]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K] [InnerProductSpace 𝕜 L]
    [CompleteSpace H] [CompleteSpace K] [CompleteSpace L]
    (S : K →L[𝕜] L) (T : H →L[𝕜] K),
    AdjointValue 𝕜 H L (S.comp T) =
      (AdjointValue 𝕜 H K T).comp (AdjointValue 𝕜 K L S)

def RangeClosure : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K),
    T.range.topologicalClosure = (AdjointValue 𝕜 H K T).ker.orthogonal

def AdjointRangeClosure : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K),
    (AdjointValue 𝕜 H K T).range.topologicalClosure = T.ker.orthogonal

def InvarianceCriterion : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)) (T : H →L[𝕜] H),
    letI : CompleteSpace M := hM.completeSpace_coe
    let P := Conventions.Spec.OrthogonalProjectionValue 𝕜 H M
    InvariantSubspaceValue 𝕜 H M T ↔ P.comp (T.comp P) = T.comp P

def ReductionCommutation : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)) (T : H →L[𝕜] H),
    letI : CompleteSpace M := hM.completeSpace_coe
    let P := Conventions.Spec.OrthogonalProjectionValue 𝕜 H M
    ReducingSubspaceValue 𝕜 H M T ↔ P.comp T = T.comp P

def ReductionAdjoint : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : Submodule 𝕜 H), IsClosed (M : Set H) → ∀ (T : H →L[𝕜] H),
    ReducingSubspaceValue 𝕜 H M T ↔
      InvariantSubspaceValue 𝕜 H M T ∧
        InvariantSubspaceValue 𝕜 H M (AdjointValue 𝕜 H H T)

def ReductionEquivalences : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : Submodule 𝕜 H) (hM : IsClosed (M : Set H)) (T : H →L[𝕜] H),
    letI : CompleteSpace M := hM.completeSpace_coe
    let P := Conventions.Spec.OrthogonalProjectionValue 𝕜 H M
    (ReducingSubspaceValue 𝕜 H M T ↔ P.comp T = T.comp P) ∧
      (P.comp T = T.comp P ↔
        InvariantSubspaceValue 𝕜 H M T ∧
          InvariantSubspaceValue 𝕜 H M (AdjointValue 𝕜 H H T))

def TransposeRieszBridge : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K) (y : K),
    (InnerProductSpace.toDual 𝕜 K y).comp T =
      InnerProductSpace.toDual 𝕜 H (AdjointValue 𝕜 H K T y)

end ExpandedFA.Hilbert.Adjoint.Spec
