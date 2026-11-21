import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02TopologicalSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Independent statements for the finite-dimensional clause of Proposition
`fa2:p1:c02:projections` (paper.tex 543–568, finite-dimensional clause).
The ambient real or complex normed space need not be complete. Subspaces
carry their inherited norms, and finite dimension includes dimension zero.
-/
namespace ExpandedFA.P1.FiniteDimensionalComplements.Spec

universe u v

/-- A bounded projection onto the original subspace, fixing it pointwise,
whose kernel is a closed topological complement. -/
def Projection : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M],
    ∃ P : E →L[𝕜] E,
      P.comp P = P ∧ P.range = M ∧
      (∀ m : M, P (m : E) = (m : E)) ∧
      IsClosed (P.ker : Set E) ∧
      C02TopologicalSum.Spec.TopologicalDirectSumValue M P.ker

/-- The manuscript's complemented predicate, with closedness of both summands
and an explicit closed complementary subspace. -/
def ClosedComplement : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M],
    IsClosed (M : Set E) ∧
      C02TopologicalSum.Spec.ComplementedValue M ∧
      ∃ N : Submodule 𝕜 E,
        IsClosed (N : Set E) ∧
        C02TopologicalSum.Spec.TopologicalDirectSumValue M N

/-- For the zero subspace the zero map itself is a suitable projection;
its complementary kernel is the whole ambient space. -/
def ZeroProjection : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    let P : E →L[𝕜] E := 0
    P.comp P = P ∧ P.range = ⊥ ∧ P.ker = ⊤ ∧
      IsClosed (P.ker : Set E) ∧
      C02TopologicalSum.Spec.TopologicalDirectSumValue (⊥ : Submodule 𝕜 E) P.ker

end ExpandedFA.P1.FiniteDimensionalComplements.Spec
