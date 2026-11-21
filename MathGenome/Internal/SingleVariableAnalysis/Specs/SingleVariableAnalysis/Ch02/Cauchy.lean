import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided

/-!
Independent specifications for K03.02.cauchy (paper.tex:409–419).
The four finite-point statements cover real/complex input and output scalars.
The eight sided/tail statements use real inputs and both scalar outputs.
Only approach points in E are tested, and both points share one neighborhood.
Side accumulation and directional unboundedness are hypotheses, as in the source.
All limits have finite values in the canonical ℝ or ℂ.
-/

namespace Specs.SingleVariableAnalysis.Ch02.Cauchy

open Specs.SingleVariableAnalysis.Ch02.RelativeLimit
open Specs.SingleVariableAnalysis.Ch02.OneSided

def realRealRelativeLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ), domainAccumulationValue E a →
    ((∃ L : ℝ, relativePuncturedLimitValue f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < |x - a| → |x - a| < δ →
          0 < |y - a| → |y - a| < δ → |f x - f y| < ε)

def realComplexRelativeLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ), domainAccumulationValue E a →
    ((∃ L : ℂ, relativePuncturedLimitValue f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < |x - a| → |x - a| < δ →
          0 < |y - a| → |y - a| < δ → ‖f x - f y‖ < ε)

def complexRealRelativeLimitCauchyCriterion : Prop :=
  ∀ (f : ℂ → ℝ) (E : Set ℂ) (a : ℂ), domainAccumulationValue E a →
    ((∃ L : ℝ, relativePuncturedLimitValue f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < ‖x - a‖ → ‖x - a‖ < δ →
          0 < ‖y - a‖ → ‖y - a‖ < δ → |f x - f y| < ε)

def complexComplexRelativeLimitCauchyCriterion : Prop :=
  ∀ (f : ℂ → ℂ) (E : Set ℂ) (a : ℂ), domainAccumulationValue E a →
    ((∃ L : ℂ, relativePuncturedLimitValue f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < ‖x - a‖ → ‖x - a‖ < δ →
          0 < ‖y - a‖ → ‖y - a‖ < δ → ‖f x - f y‖ < ε)

def realRightLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ), rightAccumulationValue E a →
    ((∃ L : ℝ, rightRelativeLimitValue f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, a < x → x < a + δ → a < y → y < a + δ → |f x - f y| < ε)

def realLeftLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ), leftAccumulationValue E a →
    ((∃ L : ℝ, leftRelativeLimitValue f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, a - δ < x → x < a → a - δ < y → y < a → |f x - f y| < ε)

def realPosInfinityLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) , domainUnboundedAboveValue E →
    ((∃ L : ℝ, limitAtPosInfinityValue f E L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, ∀ y ∈ E, A < x → A < y → |f x - f y| < ε)

def realNegInfinityLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) , domainUnboundedBelowValue E →
    ((∃ L : ℝ, limitAtNegInfinityValue f E L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, ∀ y ∈ E, x < -A → y < -A → |f x - f y| < ε)

def complexRightLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ), rightAccumulationValue E a →
    ((∃ L : ℂ, rightRelativeLimitValue f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, a < x → x < a + δ → a < y → y < a + δ → ‖f x - f y‖ < ε)

def complexLeftLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ), leftAccumulationValue E a →
    ((∃ L : ℂ, leftRelativeLimitValue f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, a - δ < x → x < a → a - δ < y → y < a → ‖f x - f y‖ < ε)

def complexPosInfinityLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) , domainUnboundedAboveValue E →
    ((∃ L : ℂ, limitAtPosInfinityValue f E L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, ∀ y ∈ E, A < x → A < y → ‖f x - f y‖ < ε)

def complexNegInfinityLimitCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) , domainUnboundedBelowValue E →
    ((∃ L : ℂ, limitAtNegInfinityValue f E L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, ∀ y ∈ E, x < -A → y < -A → ‖f x - f y‖ < ε)

end Specs.SingleVariableAnalysis.Ch02.Cauchy
