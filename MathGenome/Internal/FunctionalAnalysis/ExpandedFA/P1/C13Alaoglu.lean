import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
Banach–Alaoglu for real or complex normed spaces, including incomplete spaces.
Mathlib proves compactness of closed dual balls in its native WeakDual.
The accepted evaluation-topology identification transports that compactness
to the shared weak-star topology on the original continuous linear dual.
-/

namespace ExpandedFA.P1.C13Alaoglu

universe u v
open scoped Topology

/-- Every closed dual ball is weak-star compact, with arbitrary center and
nonnegative finite radius. No completeness of E is required. -/
theorem weakStar_closedBall_isCompact : Spec.ClosedBallCompactness.{u, v} := by
  intro 𝕜 E _ _ _ f₀ r _hr
  let e : (E →L[𝕜] 𝕜) ≃ₗ[𝕜] WeakDual 𝕜 E := StrongDual.toWeakDual
  let : TopologicalSpace (E →L[𝕜] 𝕜) :=
    C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have he : Topology.IsInducing e :=
    ⟨C12WeakStar.weakStarTopology_native 𝕜 E⟩
  have hc : IsCompact (WeakDual.toStrongDual ⁻¹' Metric.closedBall f₀ r) :=
    WeakDual.isCompact_closedBall f₀ r
  have hpre := he.isCompact_preimage' hc (by
    intro y _hy
    exact e.surjective y)
  simpa only [Set.preimage, Metric.closedBall, Set.mem_ofPred_eq, e,
    StrongDual.toStrongDual_toWeakDual, dist_eq_norm] using hpre

/-- In particular, the full closed dual unit ball is weak-star compact. -/
theorem banach_alaoglu : Spec.UnitBallCompactness.{u, v} := by
  intro 𝕜 E _ _ _
  simpa only [sub_zero] using
    weakStar_closedBall_isCompact 𝕜 E (0 : E →L[𝕜] 𝕜) 1 zero_le_one

end ExpandedFA.P1.C13Alaoglu
