import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01FiniteDimension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02TopologicalSum

/-!
Independent statements for the finite-codimensional clause of
`fa2:p1:c02:projections`, paper.tex lines 543–568.

The quotient is by the original closed subspace, with its distance quotient
norm, and the complement has its inherited norm. There is no completeness
assumption on the ambient space and no positive-codimension assumption.
`ContinuousLinearMap` records scalar linearity and boundedness in these norms.
-/

namespace ExpandedFA.P1.FiniteCodimensionalComplements.Spec

/-- A bounded section of the quotient map yields a finite-dimensional closed
topological complement. Its two bounded coordinate projections are `s q` and
`id - s q`, with their exact ranges, kernels, and decomposition identity. -/
def SectionAndComplement : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E))
    [FiniteDimensional 𝕜 (E ⧸ M)],
    letI : IsClosed (M : Set E) := hM
    ∃ s : (E ⧸ M) →L[𝕜] E,
      (∀ z, M.mkQ (s z) = z) ∧
      FiniteDimensional 𝕜 s.range ∧
      IsClosed (s.range : Set E) ∧
      Submodule.IsTopCompl M s.range ∧
      (let P := s.comp M.mkQL
       let Q := ContinuousLinearMap.id 𝕜 E - P
       P.comp P = P ∧ P.ker = M ∧ P.range = s.range ∧
       Q.comp Q = Q ∧ Q.range = M ∧ Q.ker = s.range ∧
       Q + P = ContinuousLinearMap.id 𝕜 E ∧
       ∀ x, Q x + P x = x)

/-- The original subspace is complemented, with a finite-dimensional closed
complement, in precisely the previously fixed topological direct-sum sense. -/
def FiniteDimensionalComplement : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), IsClosed (M : Set E) →
    [FiniteDimensional 𝕜 (E ⧸ M)] →
    ∃ N : Submodule 𝕜 E,
      FiniteDimensional 𝕜 N ∧ IsClosed (N : Set E) ∧
      C02TopologicalSum.Spec.TopologicalDirectSumValue M N

end ExpandedFA.P1.FiniteCodimensionalComplements.Spec
