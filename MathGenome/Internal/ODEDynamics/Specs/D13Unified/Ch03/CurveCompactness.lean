import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
The compact-interval curve compactness lemma (paper.tex, d13:03:ascoli).
The subtype `Set.Icc a b` includes both endpoints. The target is the
finite-dimensional Euclidean space ℝⁿ. Equicontinuity is the usual
pointwise equicontinuity of the entire sequence; it already implies
continuity of each curve. The convergence conclusion is uniform on the
whole interval, with a strictly increasing sequence of original indices.
-/

namespace Specs.D13Unified.Ch03

/-- The full proposition required by the curve compactness lemma. -/
def curveCompactness : Prop :=
  ∀ (n : ℕ) (a b : ℝ)
    (u : ℕ → Set.Icc a b → EuclideanSpace ℝ (Fin n)),
    (∃ M : ℝ, ∀ k t, ‖u k t‖ ≤ M) →
    Equicontinuous u →
    ∃ (φ : ℕ → ℕ) (v : Set.Icc a b → EuclideanSpace ℝ (Fin n)),
      StrictMono φ ∧ Continuous v ∧
        TendstoUniformly (fun k t => u (φ k) t) v Filter.atTop

end Specs.D13Unified.Ch03
