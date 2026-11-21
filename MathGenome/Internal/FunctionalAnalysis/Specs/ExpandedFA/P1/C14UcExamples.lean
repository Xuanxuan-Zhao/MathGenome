import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HilbertUniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.LpUniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces

/-!
Independent statements for `fa2:p1:c14:uc-examples`, paper.tex:2894–2899.
The positive clauses use the previously specified Hilbert modulus and scalar
Lᵖ quotient for arbitrary positive measures. The negative clauses concern the
canonical infinite scalar sequence spaces with their given norms, over either
ℝ or ℂ. All clauses use the same closed-unit-ball predicate.
-/
namespace ExpandedFA.P1.C14UcExamples.Spec

universe u v

/-- Includes the prescribed positive modulus and its full closed-ball estimate. -/
def HilbertModulus : Prop := HilbertUniformConvexity.Spec.ExplicitModulus.{u,v}

/-- No completeness or nontriviality is needed, so every Hilbert space is covered. -/
def HilbertUniformConvexity : Prop := HilbertUniformConvexity.Spec.UniformConvexity.{u,v}

/-- All finite real exponents p > 1, both scalar fields, and arbitrary measures. -/
def LpUniformConvexity : Prop := LpUniformConvexitySpec.MeasureUniformConvexity.{u,v}

/-- The canonical ℓ¹ norm is not uniformly convex. -/
def L1NotUniformlyConvex : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
      (C01SequenceSpaces.SequenceLp 𝕜 1)

/-- The canonical ℓ∞ norm is not uniformly convex. -/
def LInfinityNotUniformlyConvex : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
      (C01SequenceSpaces.SequenceLInfinity 𝕜)

end ExpandedFA.P1.C14UcExamples.Spec
