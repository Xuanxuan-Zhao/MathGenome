import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Higher
import Mathlib.Data.Nat.Choose.Basic

/-!
Independent specification of K03.04.leibniz (paper.tex:724–735).
The open-set statement includes every common open real interval, bounded or
unbounded. Ambient extensions represent functions on the interval, as in Higher.
Only existence of derivatives through k is assumed, including for complex
values. The conclusion includes existence of the product derivatives.
-/

namespace Specs.SingleVariableAnalysis.Ch04.Leibniz

open Set
open scoped BigOperators
universe u

def leibnizOnOpen : Prop :=
  ∀ {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (k : ℕ) (f g : ℝ → K) (I : Set ℝ), IsOpen I →
    Higher.kTimesDifferentiableOnValue k f I →
    Higher.kTimesDifferentiableOnValue k g I →
    Higher.kTimesDifferentiableOnValue k (fun x => f x * g x) I ∧
      EqOn (Higher.realIteratedDerivativeValue k (fun x => f x * g x))
        (fun x => ∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : K) * Higher.realIteratedDerivativeValue j f x *
            Higher.realIteratedDerivativeValue (k - j) g x) I

end Specs.SingleVariableAnalysis.Ch04.Leibniz
