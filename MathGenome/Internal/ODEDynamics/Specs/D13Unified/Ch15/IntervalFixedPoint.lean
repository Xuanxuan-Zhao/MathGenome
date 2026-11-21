import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Independent specification of paper.tex, Proposition `d13:15:interval-fixed-point`.
The domain and codomain are the actual closed interval, with its induced topology
and metric. Thus every iterate is defined and stays in that interval. The real
Lipschitz constant is explicitly nonnegative and may be zero. All estimates
include natural time zero.
-/

namespace Specs.D13Unified.Ch15.IntervalFixedPoint

open Filter Set
open scoped Topology
open Specs.D13Unified.Ch15.DiscreteDefinitions

/-- Every continuous self-map of a nondegenerate closed real interval has a fixed point. -/
def exists_fixedPointStatement : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (F : Icc a b → Icc a b), Continuous F →
    ∃ p : Icc a b, F p = p

/-- A contracting interval map has a unique fixed point; all its forward orbits
converge to that point and satisfy the original quantitative error estimate. -/
def contraction_fixedPointStatement : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (F : Icc a b → Icc a b), Continuous F →
    ∀ (q : ℝ), 0 ≤ q → q < 1 →
    (∀ x y : Icc a b, |(F x : ℝ) - (F y : ℝ)| ≤ q * |(x : ℝ) - (y : ℝ)|) →
    ∃ p : Icc a b, F p = p ∧
      (∀ y : Icc a b, F y = y → y = p) ∧
      (∀ x : Icc a b, Tendsto (forwardOrbit F x) atTop (𝓝 p)) ∧
      (∀ (x : Icc a b) (n : ℕ),
        |((iterate F n x : Icc a b) : ℝ) - (p : ℝ)| ≤ q ^ n * |(x : ℝ) - (p : ℝ)|)

end Specs.D13Unified.Ch15.IntervalFixedPoint
