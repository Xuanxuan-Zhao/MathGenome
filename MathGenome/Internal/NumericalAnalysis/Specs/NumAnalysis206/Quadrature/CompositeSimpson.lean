import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.PeanoKernel

/-! Independent statement of paper.tex:2157–2195, W57.
`h` is the small grid spacing; each Simpson panel has length `2*h`.
The supplied jet constrains the function only on the closed interval. -/
namespace NumAnalysis206.Quadrature.CompositeSimpsonSpec
open scoped BigOperators

noncomputable def stepValue (a b : ℝ) (n : ℕ) : ℝ := (b - a) / n
noncomputable def nodeValue (a b : ℝ) (n j : ℕ) : ℝ :=
  a + j * stepValue a b n
noncomputable def ruleValue (a b : ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  (stepValue a b n / 3) * ∑ j ∈ Finset.range (n / 2),
    (f (nodeValue a b n (2*j)) + 4 * f (nodeValue a b n (2*j+1)) +
      f (nodeValue a b n (2*j+2)))

def stepType := ℝ → ℝ → ℕ → ℝ
def nodeType := ℝ → ℝ → ℕ → ℕ → ℝ
def ruleType := ℝ → ℝ → ℕ → (ℝ → ℝ) → ℝ

def error_type : Prop :=
  ∀ {a b : ℝ} {n : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a < b → 2 ≤ n → Even n →
    ∀ hD : NumAnalysis206.Approximation.IntervalCalculusSpec.jetValue a b 4 f D,
      |(∫ t in a..b, f t) - ruleValue a b n f| ≤
        (b-a) * (stepValue a b n)^4 / 180 * ‖PeanoKernelSpec.derivativeValue hD‖

end NumAnalysis206.Quadrature.CompositeSimpsonSpec
