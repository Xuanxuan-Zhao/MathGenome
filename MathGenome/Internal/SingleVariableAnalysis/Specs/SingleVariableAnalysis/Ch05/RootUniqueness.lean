import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.IntermediateValues
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Monotonicity

/-!
Independent specifications for K03.05.root_uniqueness, paper.tex:860–869.
An ambient real function represents its restriction to [a,b]. Continuity is
relative to the entire closed interval, including its endpoints. Derivative
conditions are imposed only in (a,b), without continuity of the derivative.
Uniqueness is among all roots in [a,b], and the exhibited root lies in (a,b).
The last statement verifies the exact cubic used in the source.
-/

namespace Specs.SingleVariableAnalysis.Ch05.RootUniqueness

open Set

def rootExists : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    Ch03.Continuity.relativeContinuousValue f (Icc a b) → f a * f b < 0 →
      ∃ c ∈ Ioo a b, f c = 0

/-- Strict monotonicity includes both strict increase and strict decrease. -/
def rootUniqueStrictMonotone : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    Ch03.Continuity.relativeContinuousValue f (Icc a b) → f a * f b < 0 →
    (StrictMonoOn f (Icc a b) ∨ StrictAntiOn f (Icc a b)) →
      ∃ c ∈ Ioo a b, f c = 0 ∧ ∀ x ∈ Icc a b, f x = 0 → x = c

def rootUniquePositiveDerivative : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    Ch03.Continuity.relativeContinuousValue f (Icc a b) → f a * f b < 0 →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) →
    (∀ x ∈ Ioo a b, 0 < deriv f x) →
      ∃ c ∈ Ioo a b, f c = 0 ∧ ∀ x ∈ Icc a b, f x = 0 → x = c

def rootUniqueNegativeDerivative : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    Ch03.Continuity.relativeContinuousValue f (Icc a b) → f a * f b < 0 →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) →
    (∀ x ∈ Ioo a b, deriv f x < 0) →
      ∃ c ∈ Ioo a b, f c = 0 ∧ ∀ x ∈ Icc a b, f x = 0 → x = c

/-- The same derivative criterion in the source's relative real-increment language. -/
def rootUniqueRealIncrement : Prop :=
  ∀ (f d : ℝ → ℝ) (a b : ℝ), a < b →
    Ch03.Continuity.relativeContinuousValue f (Icc a b) → f a * f b < 0 →
    (∀ x ∈ Ioo a b,
      Ch04.Derivative.hasRealIncrementDerivativeWithinValue f (d x) (Icc a b) x) →
    ((∀ x ∈ Ioo a b, 0 < d x) ∨ (∀ x ∈ Ioo a b, d x < 0)) →
      ∃ c ∈ Ioo a b, f c = 0 ∧ ∀ x ∈ Icc a b, f x = 0 → x = c

def cubicRootCounterexample : Prop :=
  let f : ℝ → ℝ := fun x => x * (x ^ 2 - 1)
  ContinuousOn f (Icc (-2) 2) ∧
    f (-2) = -6 ∧ f 2 = 6 ∧ f (-2) * f 2 < 0 ∧
    (∀ x : ℝ, (x ∈ Ioo (-2) 2 ∧ f x = 0) ↔ x = -1 ∨ x = 0 ∨ x = 1) ∧
    ¬ (∃! x : ℝ, x ∈ Icc (-2) 2 ∧ f x = 0)

end Specs.SingleVariableAnalysis.Ch05.RootUniqueness
