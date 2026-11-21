import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.PositiveRoots
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
Independent specification of K03.01.standard_limits (paper.tex:331–344).
The source uses positive integer indices. As in the upstream sequence interface,
Lean index `n` denotes source index `n + 1`; all powers and root degrees below
therefore use `n + 1`. A fixed integer `k ≥ 0` is represented by `k : ℕ`.
The root is the upstream supremum construction, not a real-exponent expression.
-/
namespace Specs.SingleVariableAnalysis.Ch01.StandardLimits

open SequenceLimit PositiveRoots

def realGeometricDecay : Prop :=
  ∀ q : ℝ, |q| < 1 →
    realSequenceConvergesValue (fun n => q ^ (n + 1)) 0

def complexGeometricDecay : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    complexSequenceConvergesValue (fun n => q ^ (n + 1)) 0

def integerRootSelfLimit : Prop :=
  realSequenceConvergesValue
    (fun n => nonnegativeRootValue (n + 1) (n + 1 : ℕ)) 1

def polynomialOverGeometricDecay : Prop :=
  ∀ (k : ℕ) (r : ℝ), 1 < r →
    realSequenceConvergesValue (fun n => (n + 1 : ℝ) ^ k / r ^ (n + 1)) 0

end Specs.SingleVariableAnalysis.Ch01.StandardLimits
