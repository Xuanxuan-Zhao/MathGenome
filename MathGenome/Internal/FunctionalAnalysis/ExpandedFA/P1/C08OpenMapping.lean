import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08OpenMapping
import Mathlib.Analysis.Normed.Operator.Banach

/-!
The open mapping theorem and both quantitative conclusions.

Mathlib's Banach theorem uses Baire category in the complete target to
construct approximate preimages, then sums successive corrections in the
complete domain to obtain exact preimages with a uniform norm bound.
Its hypotheses allow zero spaces and do not require injectivity or a
complemented kernel. We apply its linear specialization over `RCLike`.
Openness at zero then supplies the asserted inclusion for the open unit ball.
-/

namespace ExpandedFA.P1.C08OpenMapping

theorem open_mapping : Spec.OpenMapping := by
  intro 𝕜 E F _ _ _ _ _ _ _ T hT
  exact T.isOpenMap hT

theorem open_mapping_unit_ball : Spec.UnitBallImage := by
  intro 𝕜 E F _ _ _ _ _ _ _ T hT
  have hopen : IsOpen (T '' Metric.ball (0 : E) 1) :=
    open_mapping 𝕜 E F T hT _ Metric.isOpen_ball
  have hzero : (0 : F) ∈ T '' Metric.ball (0 : E) 1 := by
    exact ⟨0, by simp, T.map_zero⟩
  exact Metric.isOpen_iff.mp hopen 0 hzero

theorem open_mapping_controlled_preimages : Spec.ControlledPreimages := by
  intro 𝕜 E F _ _ _ _ _ _ _ T hT
  exact T.exists_preimage_norm_le hT

end ExpandedFA.P1.C08OpenMapping
