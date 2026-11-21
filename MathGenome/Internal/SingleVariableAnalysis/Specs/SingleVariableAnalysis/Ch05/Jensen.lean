import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Convexity

/-!
Independent specification of K03.05.jensen (paper.tex:952–964).
Finite families are indexed by an arbitrary finite set, so this includes the
manuscript's lists of length m without requiring strictly positive weights.
An interval is an order-connected real set, including empty and degenerate ones.
No continuity or differentiability assumptions are imposed.
-/

namespace Specs.SingleVariableAnalysis.Ch05.Jensen

open scoped BigOperators

universe u

/-- The weighted point belongs to the interval and satisfies Jensen's inequality. -/
def finiteJensen : Prop :=
  ∀ {ι : Type u} (I : Set ℝ), I.OrdConnected → ∀ (f : ℝ → ℝ),
    Convexity.convexFunctionOnValue I f →
    ∀ (s : Finset ι) (w x : ι → ℝ),
      (∀ j ∈ s, 0 ≤ w j) → (∑ j ∈ s, w j) = 1 →
      (∀ j ∈ s, x j ∈ I) →
      (∑ j ∈ s, w j * x j) ∈ I ∧
        f (∑ j ∈ s, w j * x j) ≤ ∑ j ∈ s, w j * f (x j)

/-- For strict convexity equality holds exactly when the positive-weight inputs
coincide. Inputs with weight zero impose no equality condition. -/
def strictFiniteJensenEquality : Prop :=
  ∀ {ι : Type u} (I : Set ℝ), I.OrdConnected → ∀ (f : ℝ → ℝ),
    Convexity.strictConvexFunctionOnValue I f →
    ∀ (s : Finset ι) (w x : ι → ℝ),
      (∀ j ∈ s, 0 ≤ w j) → (∑ j ∈ s, w j) = 1 →
      (∀ j ∈ s, x j ∈ I) →
      (f (∑ j ∈ s, w j * x j) = ∑ j ∈ s, w j * f (x j) ↔
        ∀ j ∈ s, 0 < w j → ∀ k ∈ s, 0 < w k → x j = x k)

end Specs.SingleVariableAnalysis.Ch05.Jensen
