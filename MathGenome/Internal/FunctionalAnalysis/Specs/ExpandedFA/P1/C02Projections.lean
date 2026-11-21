import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02TopologicalSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Independent statements for the projection equivalence in Proposition
`fa2:p1:c02:projections`, paper.tex lines 543–568. Subspaces carry the inherited
norm and topology. Bounded linear maps are the native continuous linear maps,
and topological direct sums use the already identified `IsTopCompl` predicate.
There is no completeness or nontriviality assumption on the ambient space.
-/

namespace ExpandedFA.P1.C02Projections.Spec

universe u v

/-- An idempotent bounded operator splits its domain into its closed range and
kernel. Its two coordinate operators are exactly `P` and `id - P`. -/
def ProjectionDecomposition : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (P : E →L[𝕜] E),
    P.comp P = P →
      ∃ h : Submodule.IsTopCompl P.range P.ker,
        IsClosed (P.range : Set E) ∧ IsClosed (P.ker : Set E) ∧
        P.range.projectionL P.ker h = P ∧
        P.ker.projectionL P.range h.symm = ContinuousLinearMap.id 𝕜 E - P

/-- Both summands of any bounded-coordinate direct sum are closed, even in
an incomplete ambient normed space. -/
def DirectSumClosed : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M N : Submodule 𝕜 E),
    Submodule.IsTopCompl M N → IsClosed (M : Set E) ∧ IsClosed (N : Set E)

/-- The two bounded coordinate maps, viewed as endomorphisms, are projections
with precisely the indicated ranges and kernels and sum to the identity. -/
def DirectSumProjections : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M N : Submodule 𝕜 E) (h : Submodule.IsTopCompl M N),
    ∃ P Q : E →L[𝕜] E,
      P.comp P = P ∧ Q.comp Q = Q ∧
      P.range = M ∧ P.ker = N ∧ Q.range = N ∧ Q.ker = M ∧
      P + Q = ContinuousLinearMap.id 𝕜 E ∧
      (∀ x, P x = (M.projectionOntoL N h x : E) ∧
        Q x = (N.projectionOntoL M h.symm x : E))

/-- Every finite-dimensional subspace is complemented, with no completeness
assumption on the ambient space and including the zero subspace. -/
def FiniteDimensionalComplement : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M],
    C02TopologicalSum.Spec.ComplementedValue M ∧
      ∃ N : Submodule 𝕜 E,
        IsClosed (M : Set E) ∧ IsClosed (N : Set E) ∧
        Submodule.IsTopCompl M N

/-- A closed subspace whose algebraic quotient has finite dimension is
complemented. The complement can be chosen finite-dimensional and closed.
The quotient uses the original subspace, including codimension zero. -/
def FiniteCodimensionalComplement : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), IsClosed (M : Set E) →
    [FiniteDimensional 𝕜 (E ⧸ M)] →
    C02TopologicalSum.Spec.ComplementedValue M ∧
      ∃ N : Submodule 𝕜 E,
        FiniteDimensional 𝕜 N ∧ IsClosed (N : Set E) ∧
        Submodule.IsTopCompl M N

end ExpandedFA.P1.C02Projections.Spec
