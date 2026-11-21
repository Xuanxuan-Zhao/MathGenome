import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01CompactBall
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01FiniteDimension

/-!
Compact balls characterize finite dimension (`fa2:p1:c01:compact-ball`).
The converse directions use Mathlib's Riesz theorem for compact neighborhoods.
Its scalar completeness requirement is supplied by `RCLike`; the vector space
need not be complete. The forward finite-dimensional facts are reused from
the preceding accepted manuscript theorem.
-/

namespace ExpandedFA.P1.C01CompactBall

theorem compact_closed_unit_ball_iff_finite_dimensional :
    Spec.CompactClosedUnitBall := by
  intro 𝕜 E _ _ _
  constructor
  · intro h
    exact FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one h
  · intro h
    let : FiniteDimensional 𝕜 E := h
    exact (C01FiniteDimension.finite_dimensional_closed_bounded_compact 𝕜 E
      (Metric.closedBall (0 : E) 1)).mpr
      ⟨Metric.isClosed_closedBall, Metric.isBounded_closedBall⟩

theorem locally_compact_iff_finite_dimensional : Spec.LocalCompactness := by
  intro 𝕜 E _ _ _
  constructor
  · intro h
    let : LocallyCompactSpace E := h
    exact FiniteDimensional.of_locallyCompactSpace 𝕜
  · intro h
    let : FiniteDimensional 𝕜 E := h
    exact C01FiniteDimension.finite_dimensional_locally_compact 𝕜 E

end ExpandedFA.P1.C01CompactBall
