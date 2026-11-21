import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Independent statement of paper.tex, d13:06:polydisc-limit.
The norm on `Fin d → ℂ` is the maximum norm, so its balls are polydiscs.
The definition below uses actual complex coordinate monomials and absolute
convergence, rather than treating separate differentiability as holomorphy. -/
namespace D13Unified.Ch06.HolomorphicLimits

open Filter Metric Set

/-- Holomorphy in the coordinate power-series sense used in the paper.
At each point there is one polydisc inside the domain on which every target
component has an absolutely convergent series indexed by all multiindices. -/
def CoordinateHolomorphicOn {d n : ℕ} (V : Set (Fin d → ℂ))
    (f : (Fin d → ℂ) → Fin n → ℂ) : Prop :=
  ∀ a ∈ V, ∃ r : ℝ, 0 < r ∧ ball a r ⊆ V ∧
    ∀ i : Fin n, ∃ c : (Fin d → ℕ) → ℂ,
      ∀ z ∈ ball a r,
        Summable (fun α => ‖c α * ∏ j : Fin d, (z j - a j) ^ α j‖) ∧
        HasSum (fun α => c α * ∏ j : Fin d, (z j - a j) ^ α j) (f z i)

/-- Uniform convergence on each actual compact subset of the domain. -/
def CompactUniformlyOn {d n : ℕ} (V : Set (Fin d → ℂ))
    (F : ℕ → (Fin d → ℂ) → Fin n → ℂ)
    (f : (Fin d → ℂ) → Fin n → ℂ) : Prop :=
  ∀ K : Set (Fin d → ℂ), K ⊆ V → IsCompact K → TendstoUniformlyOn F f atTop K

end D13Unified.Ch06.HolomorphicLimits

namespace Specs.D13Unified.Ch06.HolomorphicLimits

open Set
open _root_.D13Unified.Ch06.HolomorphicLimits

/-- The complete original obligation, including arbitrary finite dimensions
and componentwise absolutely convergent coordinate power series. -/
def holomorphic_limit_type : Prop :=
  ∀ (d n : ℕ) (V : Set (Fin d → ℂ))
    (F : ℕ → (Fin d → ℂ) → Fin n → ℂ)
    (f : (Fin d → ℂ) → Fin n → ℂ),
    IsOpen V → (∀ k, CoordinateHolomorphicOn V (F k)) →
    CompactUniformlyOn V F f → CoordinateHolomorphicOn V f

end Specs.D13Unified.Ch06.HolomorphicLimits
