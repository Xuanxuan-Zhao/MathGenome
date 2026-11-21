import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Independent statements for the example at paper.tex:6803–6810.
The domain is the real Banach space `ℝ × ℝ`. Real division is totalized,
so the displayed quotient already has the prescribed value zero at the origin.
A directional derivative in direction `v` is the ordinary derivative at zero
of `t ↦ F (t • v)`; this includes the zero direction and is two-sided.
-/

open scoped Topology

namespace ExpandedFA.Differential.Spec

def DirectionalExampleType := (ℝ × ℝ) → ℝ

noncomputable def directionalExampleValue : DirectionalExampleType :=
  fun p => p.1 ^ 3 * p.2 / (p.1 ^ 6 + p.2 ^ 2)

def DirectionalExampleFormula : Prop :=
  directionalExampleValue 0 = 0 ∧
    ∀ p : ℝ × ℝ, p ≠ 0 →
      directionalExampleValue p = p.1 ^ 3 * p.2 / (p.1 ^ 6 + p.2 ^ 2)

def ZeroDirectionalDerivatives : Prop :=
  ∀ v : ℝ × ℝ, HasDerivAt (fun t : ℝ => directionalExampleValue (t • v)) 0 0

def ValueOnCubicCurve : Prop :=
  ∀ x : ℝ, x ≠ 0 → directionalExampleValue (x, x ^ 3) = 1 / 2

def NotContinuousAtOrigin : Prop :=
  ¬ ContinuousAt directionalExampleValue (0 : ℝ × ℝ)

def NotFrechetDifferentiableAtOrigin : Prop :=
  ¬ DifferentiableAt ℝ directionalExampleValue (0 : ℝ × ℝ)

end ExpandedFA.Differential.Spec
