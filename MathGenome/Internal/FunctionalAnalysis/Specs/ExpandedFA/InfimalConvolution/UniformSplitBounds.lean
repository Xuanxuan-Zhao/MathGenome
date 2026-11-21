import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.Definitions
import Mathlib.Analysis.Normed.Group.Bounded

/-! Independent statement of the uniform split-sublevel bound in
`fa2:p1:infconv-full-cone` (paper.tex:7160–7220). The space is real Banach;
no reflexivity or common continuity point is assumed. -/
namespace ExpandedFA.InfimalConvolution.UniformSplitBounds.Spec

open ExpandedFA.P1.ExtendedConvexFunctions

/-- Norm boundedness of all split functionals at a fixed real cost level,
uniformly over an arbitrary bounded set of total functionals (including ∅). -/
def BoundedSplitSublevels : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E),
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue E φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue E ψ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue E φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue E ψ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue E φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue E ψ →
    (Definitions.Spec.FiniteDomainValue E φ ∩
      Definitions.Spec.FiniteDomainValue E ψ).Nonempty →
    Definitions.Spec.DomainDifferenceConeValue E φ ψ = Set.univ →
    ∀ (B : Set (E →L[ℝ] ℝ)), Bornology.IsBounded B → ∀ α : ℝ,
      Bornology.IsBounded {g : E →L[ℝ] ℝ | ∃ f ∈ B,
        Definitions.Spec.ConjugateSplitCostValue E φ ψ f g ≤ (α : EReal)}

end ExpandedFA.InfimalConvolution.UniformSplitBounds.Spec
