import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.SupNorm
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Independent specification of K03.12.derivative_failure, paper.tex:1334–1339.
As in the upstream sequence interfaces, index `n` represents positive index
`n + 1`. Thus every positive integer in the source occurs, and no denominator
is zero. The canonical sine, cosine and pi are identified with the constructed
objects by the upstream SinCos and PiPeriod goals. The domain is all of ℝ.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch12.DerivativeFailure

def sineQuotientType : Type := ℕ → ℝ → ℝ

def sineQuotientValue : sineQuotientType :=
  fun n x => Real.sin ((n + 1 : ℕ) * x) / (n + 1 : ℕ)

def sineQuotientBound : Prop :=
  ∀ (n : ℕ) (x : ℝ), |sineQuotientValue n x| ≤ 1 / (n + 1 : ℕ)

def sineQuotientSupErrorBound : Prop :=
  ∀ n : ℕ, SupNorm.realSupErrorValue sineQuotientValue (fun _ => 0) n ≤
    ENNReal.ofReal (1 / (n + 1 : ℕ))

def sineQuotientUniform : Prop :=
  Uniform.realUniformConvergesValue sineQuotientValue (fun _ => 0)

def sineQuotientHasDerivAt : Prop :=
  ∀ (n : ℕ) (x : ℝ),
    HasDerivAt (sineQuotientValue n) (Real.cos ((n + 1 : ℕ) * x)) x

def sineQuotientDerivPi : Prop :=
  ∀ n : ℕ, deriv (sineQuotientValue n) Real.pi = (-1 : ℝ) ^ (n + 1)

def sineQuotientDerivNotConvergent : Prop :=
  ∀ L : ℝ, ¬ Ch01.SequenceLimit.realSequenceConvergesValue
    (fun n => deriv (sineQuotientValue n) Real.pi) L

def sineQuotientDerivNotPointwise : Prop :=
  ¬ ∃ g : ℝ → ℝ, Pointwise.realPointwiseConvergesValue
    (fun n x => deriv (sineQuotientValue n) x) g

end Specs.SingleVariableAnalysis.Ch12.DerivativeFailure
