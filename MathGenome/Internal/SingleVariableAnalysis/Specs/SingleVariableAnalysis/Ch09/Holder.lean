import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Independent statements of K03.09.holder, paper.tex:2614–2638.
Integrability and integral values are the proper Darboux objects from chapter 08.
Real norms are absolute values and complex norms are moduli. Exponents are real;
powers at zero have value zero for positive exponents. The ordered interval,
including a singleton, is already part of the integrability predicate.

The existential integrability witnesses make every integral in the inequality
well typed. The final clause explicitly covers either zero seminorm, without a
pointwise vanishing assertion. All positive absolute powers are also included.
-/
namespace Specs.SingleVariableAnalysis.Ch09.Holder
open Specs.SingleVariableAnalysis.Ch08.Integral

/-- The full inequality and its zero cases, for the ordinary scalar norm. -/
def holderEstimate {K : Type} [NormedField K] (f g : ℝ → K) (a b p q : ℝ) : Prop :=
  ∃ hfg : realIntegrableValue (fun x => ‖f x * g x‖) a b,
  ∃ hfp : realIntegrableValue (fun x => ‖f x‖ ^ p) a b,
  ∃ hgq : realIntegrableValue (fun x => ‖g x‖ ^ q) a b,
    realIntegralValue _ hfg ≤
      (realIntegralValue _ hfp) ^ (1 / p) * (realIntegralValue _ hgq) ^ (1 / q) ∧
    (((realIntegralValue _ hfp) ^ (1 / p) = 0 ∨
      (realIntegralValue _ hgq) ^ (1 / q) = 0) → realIntegralValue _ hfg = 0)

def realAbsolutePowers : Prop :=
  ∀ {f : ℝ → ℝ} {a b : ℝ}, realIntegrableValue f a b →
    ∀ r : ℝ, 0 < r → realIntegrableValue (fun x => ‖f x‖ ^ r) a b

def complexAbsolutePowers : Prop :=
  ∀ {f : ℝ → ℂ} {a b : ℝ}, complexIntegrableValue f a b →
    ∀ r : ℝ, 0 < r → realIntegrableValue (fun x => ‖f x‖ ^ r) a b

def realHolder : Prop :=
  ∀ p q : ℝ, 1 < p → 1 < q → 1 / p + 1 / q = 1 →
    ∀ {f g : ℝ → ℝ} {a b : ℝ},
      realIntegrableValue f a b → realIntegrableValue g a b →
      holderEstimate f g a b p q

def complexHolder : Prop :=
  ∀ p q : ℝ, 1 < p → 1 < q → 1 / p + 1 / q = 1 →
    ∀ {f g : ℝ → ℂ} {a b : ℝ},
      complexIntegrableValue f a b → complexIntegrableValue g a b →
      holderEstimate f g a b p q

/-- The p=q=2 instance in the usual square-root notation. -/
def cauchySchwarzEstimate {K : Type} [NormedField K] (f g : ℝ → K) (a b : ℝ) : Prop :=
  ∃ hfg : realIntegrableValue (fun x => ‖f x * g x‖) a b,
  ∃ hf2 : realIntegrableValue (fun x => ‖f x‖ ^ (2 : ℕ)) a b,
  ∃ hg2 : realIntegrableValue (fun x => ‖g x‖ ^ (2 : ℕ)) a b,
    realIntegralValue _ hfg ≤
      Real.sqrt (realIntegralValue _ hf2) * Real.sqrt (realIntegralValue _ hg2)

def realCauchySchwarz : Prop :=
  ∀ {f g : ℝ → ℝ} {a b : ℝ},
    realIntegrableValue f a b → realIntegrableValue g a b →
    cauchySchwarzEstimate f g a b

def complexCauchySchwarz : Prop :=
  ∀ {f g : ℝ → ℂ} {a b : ℝ},
    complexIntegrableValue f a b → complexIntegrableValue g a b →
    cauchySchwarzEstimate f g a b

end Specs.SingleVariableAnalysis.Ch09.Holder
