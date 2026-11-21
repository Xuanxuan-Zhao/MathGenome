import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02Projections
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Independent statements for Proposition `fa2:p1:c15:complementation`,
paper.tex 4057–4084. All subspaces carry their inherited norm and topology.
`IsCompl` expresses the algebraic direct sum, and the first statement below
identifies it with unique decomposition. Bounded projections are scalar-linear
continuous endomorphisms satisfying the literal composition identity.

The closed-complement implication uses ambient completeness. The elementary
finite-dimensional statements are stated more generally for normed spaces,
as already proved in Chapter 2. No nonzero or positive-dimension assumption
is imposed, and the finite-codimensional quotient is by the original subspace.
-/
namespace ExpandedFA.P1.C15Complementation.Spec

universe u v

/-- Algebraic direct sums mean unique decomposition into the two summands. -/
def AlgebraicSplitMeaning : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M N : Submodule 𝕜 E),
    IsCompl M N ↔ ∀ x : E, ∃! z : M × N, (z.1 : E) + (z.2 : E) = x

/-- Closed algebraic complements in a Banach space have bounded coordinates. -/
def ClosedSplitTopological : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (M N : Submodule 𝕜 E), IsClosed (M : Set E) → IsClosed (N : Set E) →
    IsCompl M N → C02TopologicalSum.Spec.TopologicalDirectSumValue M N

/-- The projection belonging to each specified closed split is its first coordinate. -/
def ClosedSplitProjection : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (M N : Submodule 𝕜 E), IsClosed (M : Set E) → IsClosed (N : Set E) →
    IsCompl M N → ∃ P : E →L[𝕜] E,
      P.comp P = P ∧ P.range = M ∧ P.ker = N ∧
        ∀ (m : M) (n : N), P ((m : E) + (n : E)) = (m : E)

/-- Any bounded projection gives a closed split and is its coordinate map.
This direction does not require ambient completeness. -/
def IdempotentClosedSplit : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (P : E →L[𝕜] E),
    P.comp P = P →
      P.range = (ContinuousLinearMap.id 𝕜 E - P).ker ∧
      IsClosed (P.range : Set E) ∧ IsClosed (P.ker : Set E) ∧
      IsCompl P.range P.ker ∧
      (∀ x : E, ∃! z : P.range × P.ker, (z.1 : E) + (z.2 : E) = x) ∧
      (∀ x : E, x - P x ∈ P.ker ∧ P x + (x - P x) = x) ∧
      ∀ (m : P.range) (n : P.ker), P ((m : E) + (n : E)) = (m : E)

/-- The source equivalence for the original closed subspace of a Banach space. -/
def ProjectionClosedComplementIff : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (M : Submodule 𝕜 E), IsClosed (M : Set E) →
    ((∃ P : E →L[𝕜] E, P.comp P = P ∧ P.range = M) ↔
      ∃ N : Submodule 𝕜 E, IsClosed (N : Set E) ∧ IsCompl M N)

/-- Closed Hilbert subspaces admit bounded projections and topological complements. -/
def HilbertSubspaceProjection : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : Submodule 𝕜 H), IsClosed (M : Set H) →
    C02TopologicalSum.Spec.ComplementedValue M ∧
      ∃ P : H →L[𝕜] H, P.comp P = P ∧ P.range = M

/-- Finite-dimensional subspaces are complemented, including dimension zero. -/
def FiniteDimensionalSubspaceProjection : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M],
    C02TopologicalSum.Spec.ComplementedValue M ∧
      ∃ P : E →L[𝕜] E, P.comp P = P ∧ P.range = M

/-- Closed subspaces of finite codimension are complemented, including codimension zero. -/
def FiniteCodimensionalSubspaceProjection : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), IsClosed (M : Set E) →
    ∀ [FiniteDimensional 𝕜 (E ⧸ M)],
      C02TopologicalSum.Spec.ComplementedValue M ∧
        ∃ P : E →L[𝕜] E, P.comp P = P ∧ P.range = M

end ExpandedFA.P1.C15Complementation.Spec
