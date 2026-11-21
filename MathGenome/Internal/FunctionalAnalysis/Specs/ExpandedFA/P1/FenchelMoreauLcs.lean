import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.LcsStrongSeparation

/-! Independent specification of `fa2:p1:fenchel-moreau-lcs`, paper.tex:5205–5213.
The domain has its given Hausdorff locally convex topology, without a norm or
completeness assumption. The primal values are the shared `WithTop ℝ` values;
both conjugation suprema use `EReal`, with exactly the chapter 6 conventions.
-/
namespace ExpandedFA.P1.FenchelMoreauLcs.Spec

open ExtendedConvexFunctions

def ConvexConjugateType :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
    ExtendedFunction E → (E →L[ℝ] ℝ) → EReal

noncomputable def ConvexConjugateValue : ConvexConjugateType :=
  fun _ _ _ _ φ f =>
    ⨆ x, (f x : EReal) - C06Conjugates.Spec.ExtendedRealValueValue (φ x)

def ConvexBiconjugateType :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
    ExtendedFunction E → E → EReal

noncomputable def ConvexBiconjugateValue : ConvexBiconjugateType :=
  fun E _ _ _ φ x =>
    ⨆ f : E →L[ℝ] ℝ, (f x : EReal) - ConvexConjugateValue E φ f

/-- The extension agrees with the previously specified normed-space conjugate. -/
def NormedConjugateAgreement : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E) (f : E →L[ℝ] ℝ),
    ConvexConjugateValue E φ f = C06Conjugates.Spec.ConvexConjugateValue E φ f

def NormedBiconjugateAgreement : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E) (x : E),
    ConvexBiconjugateValue E φ x = C06Conjugates.Spec.ConvexBiconjugateValue E φ x

/-- The full equality, including points with primal value +∞. -/
def FenchelMoreau : Prop :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (φ : ExtendedFunction E),
    ExtendedConvexFunctions.Spec.ProperValue E φ →
    ExtendedConvexFunctions.Spec.ExtendedConvexValue E φ →
    ExtendedConvexFunctions.Spec.LowerSemicontinuousValue E φ →
    ∀ x : E, ConvexBiconjugateValue E φ x =
      C06Conjugates.Spec.ExtendedRealValueValue (φ x)

end ExpandedFA.P1.FenchelMoreauLcs.Spec
