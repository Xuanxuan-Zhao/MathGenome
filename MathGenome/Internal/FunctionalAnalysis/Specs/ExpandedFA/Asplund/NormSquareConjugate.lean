import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates

/-! The norm-square conjugacy used in paper.tex:7032–7036 and 7053.
The norm is given on the original real vector space. Quantitative equivalence
keeps its continuous dual equal to the reference continuous dual. Neither
completeness nor norm attainment nor a nonzero space is required. -/
namespace ExpandedFA.Asplund.NormSquareConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordinary norm axioms and two-sided equivalence to the reference norm. -/
def EquivalentNorm (p : E → ℝ) : Prop :=
  P1.C01Norm.NormAxioms ℝ p ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ x : E, a * ‖x‖ ≤ p x ∧ p x ≤ b * ‖x‖

/-- The dual norm on the *same* continuous linear dual, using absolute values. -/
noncomputable def dualNorm (p : E → ℝ) (f : E →L[ℝ] ℝ) : ℝ :=
  sSup ((fun x => |f x|) '' {x : E | p x ≤ 1})

/-- The everywhere-finite half-squared norm, in the shared extended-function type. -/
noncomputable def halfNormSquare (p : E → ℝ) : P1.ExtendedConvexFunctions.ExtendedFunction E :=
  fun x => ((p x ^ 2 / 2 : ℝ) : WithTop ℝ)

namespace Spec

/-- In particular, the real supremum defining the dual norm is well founded. -/
def DualNormIsLUB : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E → ℝ), EquivalentNorm p → ∀ f : E →L[ℝ] ℝ,
    IsLUB ((fun x => |f x|) '' {x : E | p x ≤ 1}) (dualNorm p f)

/-- Equality with the conjugate of the accepted, reference-topology interface. -/
def Conjugacy : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E → ℝ), EquivalentNorm p → ∀ f : E →L[ℝ] ℝ,
    P1.C06Conjugates.Spec.ConvexConjugateValue E (halfNormSquare p) f =
      ((dualNorm p f ^ 2 / 2 : ℝ) : EReal)

end Spec
end ExpandedFA.Asplund.NormSquareConjugate
