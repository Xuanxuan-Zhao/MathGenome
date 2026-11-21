import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.Lagrange
import Mathlib.Analysis.Convex.Hull

/-! W50, paper.tex:1835–1855. Derivatives are the supplied closed-interval
jet, so endpoints and singleton intervals require no ambient extension. -/
namespace NumAnalysis206.Approximation.LagrangeRemainderSpec
open Set Polynomial

/-- Lagrange's remainder for `n + 1` distinct nodes in a real closed interval.
The finite convex hull is already closed. The evaluation point may be a node. -/
def lagrange_remainder_type : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (nodes : ι → ℝ)
    (n : ℕ) (a b : ℝ) (f : ℝ → ℝ) (D : ℕ → ℝ → ℝ) (x : ℝ),
    a ≤ b → s.card = n + 1 → InjOn nodes s →
    (∀ i ∈ s, nodes i ∈ Icc a b) → x ∈ Icc a b →
    IntervalCalculusSpec.jetValue a b (n + 1) f D →
    ∃ ξ ∈ convexHull ℝ (insert x (nodes '' (s : Set ι))),
      f x - (Specs.NumAnalysis206.Approximation.interpolantValue s nodes (f ∘ nodes)).eval x =
        D (n + 1) ξ / (n + 1).factorial * ∏ i ∈ s, (x - nodes i)

end NumAnalysis206.Approximation.LagrangeRemainderSpec
