import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Instances.Real.Lemmas

/-! The exact central stencil example of W61, paper.tex:2438–2456.
Derivatives are taken within the fixed closed neighborhood. Its finite
smoothness convention imposes no condition outside that neighborhood. -/
noncomputable section
namespace Specs.NumAnalysis206.Quadrature.CentralRichardson
open Set Filter Asymptotics Topology

def centralDifferenceValue (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f (x - h)) / (2 * h)

def centralDifferenceType := (ℝ → ℝ) → ℝ → ℝ → ℝ

def extrapolatedCentralValue (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (4 * centralDifferenceValue f x (h / 2) - centralDifferenceValue f x h) / 3

def extrapolatedCentralType := (ℝ → ℝ) → ℝ → ℝ → ℝ

/-- The supremum is over the full allowed neighborhood, uniformly in `h`. -/
def fifthDerivativeSupValue (f : ℝ → ℝ) (x H : ℝ) : ℝ :=
  sSup ((fun t => |iteratedDerivWithin 5 f (Icc (x - H) (x + H)) t|) ''
    Icc (x - H) (x + H))

def fifthDerivativeSupType := (ℝ → ℝ) → ℝ → ℝ → ℝ

def expansion : Prop :=
  ∀ {f : ℝ → ℝ} {x H : ℝ}, 0 < H →
    NumAnalysis206.Approximation.IntervalCalculusSpec.smoothValue (x - H) (x + H) 5 f →
    ∃ r : ℝ → ℝ, ∀ h : ℝ, 0 < h → h ≤ H →
      centralDifferenceValue f x h =
        deriv f x +
        iteratedDeriv 3 f x * h ^ 2 / 6 + r h ∧
      |r h| ≤ fifthDerivativeSupValue f x H * h ^ 4 / 120

def bound : Prop :=
  ∀ {f : ℝ → ℝ} {x H h : ℝ}, 0 < H →
    NumAnalysis206.Approximation.IntervalCalculusSpec.smoothValue (x - H) (x + H) 5 f →
    0 < h → h ≤ H →
    |extrapolatedCentralValue f x h -
      deriv f x| ≤
      fifthDerivativeSupValue f x H * h ^ 4 / 288

def fourthOrder : Prop :=
  ∀ {f : ℝ → ℝ} {x H : ℝ}, 0 < H →
    NumAnalysis206.Approximation.IntervalCalculusSpec.smoothValue (x - H) (x + H) 5 f →
    (fun h => extrapolatedCentralValue f x h -
      deriv f x) =O[𝓝[Ioi 0] 0]
      (fun h : ℝ => h ^ 4)

end Specs.NumAnalysis206.Quadrature.CentralRichardson
