import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates

/-! Independent statements for Example `fa2:p1:c06:conjugate-examples`,
paper.tex 1346–1357. All suprema use the full extended real line, and
the original functions have values in the reals with +∞ adjoined. -/
namespace ExpandedFA.P1.C06ConjugateExamples.Spec

open ExpandedFA.P1.ExtendedConvexFunctions

def NormFunctionType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E], ExtendedFunction E

def NormFunctionValue : NormFunctionType := fun _ _ _ x => (‖x‖ : WithTop ℝ)

def ConvexIndicatorType := ∀ (E : Type*), Set E → ExtendedFunction E

noncomputable def ConvexIndicatorValue : ConvexIndicatorType :=
  fun _ C x => by classical exact if x ∈ C then 0 else ⊤

def SupportFunctionType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    Set E → (E →L[ℝ] ℝ) → EReal

noncomputable def SupportFunctionValue : SupportFunctionType :=
  fun _ _ _ C f => ⨆ x : C, (f x : EReal)

/-- The closed dual unit ball includes its boundary and the zero dual. -/
def NormConjugate : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E →L[ℝ] ℝ),
    ExpandedFA.P1.C06Conjugates.Spec.ConvexConjugateValue E (NormFunctionValue E) f =
      if ‖f‖ ≤ 1 then 0 else ⊤

/-- The formula even holds for an arbitrary set, with empty supremum −∞. -/
def IndicatorConjugate : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (f : E →L[ℝ] ℝ),
    ExpandedFA.P1.C06Conjugates.Spec.ConvexConjugateValue E (ConvexIndicatorValue E C) f =
      SupportFunctionValue E C f

/-- No boundedness, interior, or completeness assumption is imposed. -/
def IndicatorBiconjugate : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    ∀ x : E,
      ExpandedFA.P1.C06Conjugates.Spec.ConvexBiconjugateValue E (ConvexIndicatorValue E C) x =
        ExpandedFA.P1.C06Conjugates.Spec.ExtendedRealValueValue (ConvexIndicatorValue E C x)

end ExpandedFA.P1.C06ConjugateExamples.Spec
