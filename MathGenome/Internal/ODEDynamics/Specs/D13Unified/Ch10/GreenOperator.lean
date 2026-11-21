import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.GreenWeakInverse
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Independent full operator assertions of paper.tex, d13:10:green.
The operator is the already defined integral operator on the weighted L²
quotient. No positivity, injectivity, or compactness certificate is input. -/
noncomputable section
open MeasureTheory Set

namespace Specs.D13Unified.Ch10.GreenOperator
open _root_.D13Unified.Ch10.GreenKernel
open RegularProblem hiding Problem
open GreenWeakInverse

def Linearity : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  (∀ f g : hilbertValue P, operatorValue P c (f + g) =
    operatorValue P c f + operatorValue P c g) ∧
  (∀ (z : ℂ) (f : hilbertValue P), operatorValue P c (z • f) =
    z • operatorValue P c f)

def BoundedLinear : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∃ K : hilbertValue P →L[ℂ] hilbertValue P, ∀ f, K f = operatorValue P c f

def Compact : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  IsCompactOperator (operatorValue P c)

def SelfAdjoint : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∀ f g : hilbertValue P,
    paperInnerValue P (operatorValue P c f) g =
      paperInnerValue P f (operatorValue P c g)

def Injective : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  Function.Injective (operatorValue P c)

def StrictlyPositive : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∀ f : hilbertValue P, f ≠ 0 →
    0 < (paperInnerValue P (operatorValue P c f) f).re ∧
    (paperInnerValue P (operatorValue P c f) f).im = 0

/-- The real energy uses the actual Green representative and its derivative
within the actual interval, hence includes the one-sided endpoint convention. -/
def EnergyIdentity : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∀ f : hilbertValue P,
    paperInnerValue P (operatorValue P c f) f =
      ((∫ x in P.a..P.b,
        P.p x * ‖derivativeValue P (representativeValue P c f) x‖ ^ 2 +
          Q P c x * ‖representativeValue P c f x‖ ^ 2 : ℝ) : ℂ)

end Specs.D13Unified.Ch10.GreenOperator
