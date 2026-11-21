import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Bernstein
import Mathlib.Topology.ContinuousMap.Compact

/-!
Independent specification of K03.16.bernstein_convergence, paper.tex:3888–3902.
The modulus is the supremum of all differences at pairs in the closed unit
interval whose real distance is at most δ. The norm is the canonical supremum
norm on continuous maps. The approximation values are the upstream finite sums;
no convergence or estimate is included in the definitions.
-/
noncomputable section
open scoped unitInterval Topology

namespace Specs.SingleVariableAnalysis.Ch16.BernsteinConvergence

def modulusType := {E : Type} → [NormedAddCommGroup E] → C(I, E) → ℝ → ℝ

def modulusValue : modulusType := fun f δ =>
  sSup {r : ℝ | ∃ x y : I, |(x : ℝ) - y| ≤ δ ∧ r = ‖f x - f y‖}

def realEstimate : Prop := ∀ (f : C(I, ℝ)) (n : ℕ), 1 ≤ n →
  ∀ δ : ℝ, 0 < δ →
    ‖Bernstein.realApproximationValue n f - f‖ ≤
      modulusValue f δ + ‖f‖ / (2 * (n : ℝ) * δ ^ 2)

def complexEstimate : Prop := ∀ (f : C(I, ℂ)) (n : ℕ), 1 ≤ n →
  ∀ δ : ℝ, 0 < δ →
    ‖Bernstein.complexApproximationValue n f - f‖ ≤
      modulusValue f δ + ‖f‖ / (2 * (n : ℝ) * δ ^ 2)

def realUniformConvergence : Prop := ∀ f : C(I, ℝ),
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x : I,
    |Bernstein.realApproximationValue n f x - f x| < ε

def complexUniformConvergence : Prop := ∀ f : C(I, ℂ),
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x : I,
    ‖Bernstein.complexApproximationValue n f x - f x‖ < ε

end Specs.SingleVariableAnalysis.Ch16.BernsteinConvergence
