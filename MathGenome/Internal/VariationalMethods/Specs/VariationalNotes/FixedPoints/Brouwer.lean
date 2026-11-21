import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent specification of paper.tex, Theorem 10.3
(`thm:brouwer-compact-convex`). Subsets carry the topology induced by the
ambient norm. No positive-dimension or interior hypothesis is imposed. -/

namespace Specs.VariationalNotes.FixedPoints

universe u

/-- Every continuous self-map of a nonempty compact convex subset of a
finite-dimensional real normed space has a fixed point. -/
def brouwer_compact_convex : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E),
    K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ F : K → K, Continuous F → ∃ x : K, F x = x

end Specs.VariationalNotes.FixedPoints
