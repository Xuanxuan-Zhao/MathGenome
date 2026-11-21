import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero
import Mathlib.Analysis.Complex.Basic

/-! Independent statements for paper.tex:5502–5504.
The norm is the uniform norm of the native bounded continuous representative.
The complex positivity hypothesis spells out exactly the nonnegative real cone.
No continuity of the linear functional is assumed. -/

namespace Specs.D11.Ch19.PositiveFunctionalBound
universe u

/-- Positivity bounds a real linear functional on each compact support. -/
def real_bound : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ),
    (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f) →
    ∀ K : Set X, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : CompactlySupportedContinuousMap X ℝ,
        closure {x | f x ≠ 0} ⊆ K →
          |I f| ≤ C * ‖f.toBoundedContinuousFunction‖

/-- The same local bound for complex linear functionals positive on real functions. -/
def complex_bound : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ),
    (∀ f, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (I f).re ∧ (I f).im = 0) →
    ∀ K : Set X, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : CompactlySupportedContinuousMap X ℂ,
        closure {x | f x ≠ 0} ⊆ K →
          ‖I f‖ ≤ C * ‖f.toBoundedContinuousFunction‖

end Specs.D11.Ch19.PositiveFunctionalBound
