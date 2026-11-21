import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ExtendedConvexFunctions
import Mathlib.Analysis.Normed.Operator.Basic

/-! Continuous affine minorants in paper.tex, lines 1302–1337.
The extended codomain contains +∞ and excludes −∞. The `IsLUB` statement
expresses the pointwise supremum without choosing an artificial empty supremum.
No completeness or interior hypothesis is imposed on the real normed space. -/
namespace ExpandedFA.P1.AffineMinorants
open ExpandedFA.P1.ExtendedConvexFunctions
universe u

/-- The real affine function `y ↦ h y + c` is everywhere below `φ`. -/
def IsContinuousAffineMinorant {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E) (h : E →L[ℝ] ℝ) (c : ℝ) : Prop :=
  ∀ y, ((h y + c : ℝ) : WithTop ℝ) ≤ φ y

namespace Spec
open ExpandedFA.P1.ExtendedConvexFunctions.Spec

def Existence : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ExtendedFunction E),
    ProperValue E φ → ExtendedConvexValue E φ → LowerSemicontinuousValue E φ →
    ∃ (h : E →L[ℝ] ℝ) (c : ℝ), IsContinuousAffineMinorant φ h c

def StrictApproximation : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ExtendedFunction E),
    ProperValue E φ → ExtendedConvexValue E φ → LowerSemicontinuousValue E φ →
    ∀ (x : E) (t : ℝ), (t : WithTop ℝ) < φ x →
    ∃ (h : E →L[ℝ] ℝ) (c : ℝ), IsContinuousAffineMinorant φ h c ∧ t < h x + c

def PointwiseSupremum : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ExtendedFunction E),
    ProperValue E φ → ExtendedConvexValue E φ → LowerSemicontinuousValue E φ →
    ∀ x : E, IsLUB {r : WithTop ℝ | ∃ (h : E →L[ℝ] ℝ) (c : ℝ),
      IsContinuousAffineMinorant φ h c ∧ r = ((h x + c : ℝ) : WithTop ℝ)} (φ x)

end Spec
end ExpandedFA.P1.AffineMinorants
