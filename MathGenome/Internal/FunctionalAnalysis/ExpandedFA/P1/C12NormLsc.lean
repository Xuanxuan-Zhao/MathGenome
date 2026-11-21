import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12NormLsc
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.WeakClosedBalls

/-!
Finite sublevels are horizontal slices of the convex epigraph. Their norm
closedness therefore transfers to the weak topology by the convex-closure
theorem. The sublevel at +∞ is the whole space.
-/

namespace ExpandedFA.P1.C12NormLsc

universe u v

theorem convex_weak_lowerSemicontinuous :
    Spec.ConvexWeakLowerSemicontinuous.{u,v} := by
  intro 𝕜 E _ _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro Φ hconv hlsc
  apply (@lowerSemicontinuous_iff_isClosed_preimage E
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
      (topDualPairing 𝕜 E)) (WithTop ℝ) _ Φ).mpr
  intro r
  cases r using WithTop.recTopCoe with
  | top =>
      simp only [Set.Iic_top, Set.preimage_univ]
      exact @isClosed_univ E
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
          (topDualPairing 𝕜 E))
  | coe r =>
      apply C12ConvexClosure.isWeaklyClosed_of_isClosed_convex 𝕜 E
      · intro x hx y hy a b ha hb hab
        have h := hconv (x := (x, r)) (y := (y, r)) hx hy ha hb hab
        change Φ (a • x + b • y) ≤ ((a * r + b * r : ℝ) : WithTop ℝ) at h
        change Φ (a • x + b • y) ≤ (r : WithTop ℝ)
        simpa only [← add_mul, hab, one_mul] using h
      · exact hlsc.isClosed_preimage (r : WithTop ℝ)

theorem weak_closed_balls : Spec.WeakClosedBalls.{u,v} :=
  WeakClosedBalls.weak_closed_balls

theorem weakStar_closed_balls : Spec.WeakStarClosedBalls.{u,v} :=
  WeakClosedBalls.weakStar_closed_balls

end ExpandedFA.P1.C12NormLsc
