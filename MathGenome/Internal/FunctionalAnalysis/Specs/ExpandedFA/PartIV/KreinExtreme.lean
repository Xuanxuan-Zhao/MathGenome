import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinEven
import Mathlib.Analysis.Convex.Extreme

/-! The normalized class in the extreme-function part of `fa2:p4:krein-even`.
No uniqueness of the general representing measure is imposed. -/
noncomputable section
open Set
namespace ExpandedFA.PartIV.KreinExtreme.Spec
open KreinSolutions.Specs

/-- All continuous real even functions with the original even-test positivity
and value one at zero. -/
def normalized : Set (ℝ → ℝ) :=
  {p | Continuous p ∧ Function.Even p ∧ KreinEven.Spec.EvenTestPositive p ∧ p 0 = 1}

def NormalizedConvex : Prop := Convex ℝ normalized

def SpectralInjectivity : Prop := Function.Injective CValue

def ScalarExtremality : Prop :=
  ∀ μ : ℝ, CValue μ ∈ normalized.extremePoints ℝ

def Exhaustion : Prop :=
  ∀ p ∈ normalized.extremePoints ℝ, ∃ μ : ℝ, p = CValue μ

def Classification : Prop :=
  ∀ p : ℝ → ℝ, p ∈ normalized.extremePoints ℝ ↔
    (∃ a : ℝ, 0 ≤ a ∧ p = fun s => Real.cos (a * s)) ∨
    (∃ b : ℝ, 0 < b ∧ p = fun s => Real.cosh (b * s))

end ExpandedFA.PartIV.KreinExtreme.Spec
