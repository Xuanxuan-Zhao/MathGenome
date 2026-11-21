import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.PeanoKernel

/-! Independent statements of W56 (paper.tex:2121–2155).
The derivative norm is the uniform norm on the original closed interval.
All finite derivative data use the shared one-sided endpoint convention. -/
namespace NumAnalysis206.Quadrature.CompositeMidpointTrapezoidSpec
open Set
open scoped BigOperators

noncomputable def stepValue (a b : ℝ) (n : ℕ) : ℝ := (b - a) / n
noncomputable def nodeValue (a b : ℝ) (n j : ℕ) : ℝ := a + j * stepValue a b n
noncomputable def midpointValue (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  stepValue a b n * ∑ j ∈ Finset.range n,
    f ((nodeValue a b n j + nodeValue a b n (j + 1)) / 2)
noncomputable def trapezoidValue (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  (stepValue a b n / 2) * ∑ j ∈ Finset.range n,
    (f (nodeValue a b n j) + f (nodeValue a b n (j + 1)))

def stepType := ℝ → ℝ → ℕ → ℝ
def nodeType := ℝ → ℝ → ℕ → ℕ → ℝ
def ruleType := (ℝ → ℝ) → ℝ → ℝ → ℕ → ℝ

def midpoint_type : Prop :=
  ∀ {a b : ℝ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ} (n : ℕ),
    a < b → 1 ≤ n →
    ∀ hD : NumAnalysis206.Approximation.IntervalCalculusSpec.jetValue a b 2 f D,
      |(∫ t in a..b, f t) - midpointValue f a b n| ≤
        (b - a) * (stepValue a b n) ^ 2 / 24 * ‖PeanoKernelSpec.derivativeValue hD‖

def trapezoid_type : Prop :=
  ∀ {a b : ℝ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ} (n : ℕ),
    a < b → 1 ≤ n →
    ∀ hD : NumAnalysis206.Approximation.IntervalCalculusSpec.jetValue a b 2 f D,
      |(∫ t in a..b, f t) - trapezoidValue f a b n| ≤
        (b - a) * (stepValue a b n) ^ 2 / 12 * ‖PeanoKernelSpec.derivativeValue hD‖

end NumAnalysis206.Quadrature.CompositeMidpointTrapezoidSpec
