import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.Topology.Order.Compact

/-! The bounds of paper.tex, W60. Derivatives are the supplied continuous
closed-interval derivative data; in particular the forward derivative at `x`
has the right-sided interpretation. The supremum is over the whole stencil. -/
namespace NumAnalysis206.Quadrature.FiniteDifferenceSpec
open Set
open NumAnalysis206.Approximation.IntervalCalculusSpec

def central_bound_type : Prop :=
  ∀ {x h η M : ℝ} {f y : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    0 < h → 0 ≤ η → jetValue (x - h) (x + h) 3 f D →
    (∀ t ∈ Icc (x - h) (x + h), |D 3 t| ≤ M) →
    |y (x + h) - f (x + h)| ≤ η → |y (x - h) - f (x - h)| ≤ η →
    |(y (x + h) - y (x - h)) / (2 * h) - D 1 x| ≤ M * h ^ 2 / 6 + η / h

def forward_bound_type : Prop :=
  ∀ {x h η M : ℝ} {f y : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    0 < h → 0 ≤ η → jetValue x (x + h) 2 f D →
    (∀ t ∈ Icc x (x + h), |D 2 t| ≤ M) →
    |y (x + h) - f (x + h)| ≤ η → |y x - f x| ≤ η →
    |(y (x + h) - y x) / h - D 1 x| ≤ M * h / 2 + 2 * η / h

def central_sup_type : Prop :=
  ∀ {x h η : ℝ} {f y : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    0 < h → 0 ≤ η → jetValue (x - h) (x + h) 3 f D →
    |y (x + h) - f (x + h)| ≤ η → |y (x - h) - f (x - h)| ≤ η →
    |(y (x + h) - y (x - h)) / (2 * h) - D 1 x| ≤
      sSup ((fun t => |D 3 t|) '' Icc (x - h) (x + h)) * h ^ 2 / 6 + η / h

def forward_sup_type : Prop :=
  ∀ {x h η : ℝ} {f y : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    0 < h → 0 ≤ η → jetValue x (x + h) 2 f D →
    |y (x + h) - f (x + h)| ≤ η → |y x - f x| ≤ η →
    |(y (x + h) - y x) / h - D 1 x| ≤
      sSup ((fun t => |D 2 t|) '' Icc x (x + h)) * h / 2 + 2 * η / h

end NumAnalysis206.Quadrature.FiniteDifferenceSpec
