import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-! Independent specification of K03.05.lhopital_infinite, paper.tex:903–922.
An open interval is any open order-connected real set, including rays and ℝ.
The finite endpoint is excluded from the interval; side accumulation, or
unboundedness in the selected direction, is explicitly required. Functions
are ambient extensions and are tested only on the interval. -/
namespace SingleVariableAnalysis

/-- A specified one-sided endpoint approach on an open real interval. -/
def IsOpenIntervalEndpoint (J : Set ℝ) (q : RealApproach) : Prop :=
  IsOpen J ∧ Set.OrdConnected J ∧
    Specs.SingleVariableAnalysis.Ch02.OneSided.approachNontrivialValue J q ∧
    match q with
    | .punctured _ => False
    | .right a => a ∉ J
    | .left a => a ∉ J
    | .posInfinity => True
    | .negInfinity => True

end SingleVariableAnalysis

namespace Specs.SingleVariableAnalysis.Ch05.LhopitalInfinite
open _root_.SingleVariableAnalysis
open Ch02.OneSided

/-- Nonvanishing follows from absolute divergence alone. -/
def eventuallyNonzero : Prop :=
  ∀ (g : ℝ → ℝ) (J : Set ℝ) (q : RealApproach),
    (∀ B : ℝ, approachEventuallyValue J q (fun x => B < |g x|)) →
    approachEventuallyValue J q (fun x => g x ≠ 0)

/-- Finite derivative-ratio limit; no limit of the numerator is assumed. -/
def finiteLimit : Prop :=
  ∀ (f g : ℝ → ℝ) (J : Set ℝ) (q : RealApproach) (L : ℝ),
    IsOpenIntervalEndpoint J q →
    (∀ x ∈ J, DifferentiableAt ℝ f x) →
    (∀ x ∈ J, DifferentiableAt ℝ g x) →
    (∀ x ∈ J, deriv g x ≠ 0) →
    (∀ B : ℝ, approachEventuallyValue J q (fun x => B < |g x|)) →
    finiteApproachLimitValue (fun x => deriv f x / deriv g x) J q L →
    approachEventuallyValue J q (fun x => g x ≠ 0) ∧
      finiteApproachLimitValue (fun x => f x / g x) J q L

/-- The extended limit +∞. -/
def posInfinityLimit : Prop :=
  ∀ (f g : ℝ → ℝ) (J : Set ℝ) (q : RealApproach),
    IsOpenIntervalEndpoint J q →
    (∀ x ∈ J, DifferentiableAt ℝ f x) →
    (∀ x ∈ J, DifferentiableAt ℝ g x) →
    (∀ x ∈ J, deriv g x ≠ 0) →
    (∀ B : ℝ, approachEventuallyValue J q (fun x => B < |g x|)) →
    realLimitToPosInfinityValue (fun x => deriv f x / deriv g x) J q →
    approachEventuallyValue J q (fun x => g x ≠ 0) ∧
      realLimitToPosInfinityValue (fun x => f x / g x) J q

/-- The extended limit -∞. -/
def negInfinityLimit : Prop :=
  ∀ (f g : ℝ → ℝ) (J : Set ℝ) (q : RealApproach),
    IsOpenIntervalEndpoint J q →
    (∀ x ∈ J, DifferentiableAt ℝ f x) →
    (∀ x ∈ J, DifferentiableAt ℝ g x) →
    (∀ x ∈ J, deriv g x ≠ 0) →
    (∀ B : ℝ, approachEventuallyValue J q (fun x => B < |g x|)) →
    realLimitToNegInfinityValue (fun x => deriv f x / deriv g x) J q →
    approachEventuallyValue J q (fun x => g x ≠ 0) ∧
      realLimitToNegInfinityValue (fun x => f x / g x) J q

end Specs.SingleVariableAnalysis.Ch05.LhopitalInfinite
