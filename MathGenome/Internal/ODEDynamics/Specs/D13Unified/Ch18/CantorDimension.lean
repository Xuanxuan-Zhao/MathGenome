import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.CantorGeometry
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.CantorMeasureEstimate
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.HausdorffDefinitions

/-! Independent statements for paper.tex, Theorem d13:18:cantor-dimension.
The set is the range of the canonical binary series. Hausdorff measure uses
the diameter-power normalization fixed upstream. `hasBoxDimension_value`
asserts a limit through every positive real mesh, not just geometric meshes. -/

namespace Specs.D13Unified.Ch18.CantorDimension
open Specs.D13Unified.Ch17.CantorGeometry
open Specs.D13Unified.Ch18.HausdorffDefinitions
open Specs.D13Unified.Ch18.CantorMeasureEstimate
noncomputable section

def cantor_dimensionStatement : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 / 2 →
    hausdorffDimension_value (cantorSet r) = ENNReal.ofReal (exponent r) ∧
    hasBoxDimension_value (cantorSet r) (exponent r) ∧
    boxDimension_value (cantorSet r) = some (exponent r) ∧
    0 < hausdorffMeasure_value (exponent r) (cantorSet r) ∧
    hausdorffMeasure_value (exponent r) (cantorSet r) < ⊤

/-- `C_(1/3)` is the middle-thirds set in the source's binary-series notation. -/
def middle_thirds_dimensionStatement : Prop :=
  hausdorffDimension_value (cantorSet (1 / 3)) =
      ENNReal.ofReal (Real.log 2 / Real.log 3) ∧
    hasBoxDimension_value (cantorSet (1 / 3)) (Real.log 2 / Real.log 3) ∧
    boxDimension_value (cantorSet (1 / 3)) = some (Real.log 2 / Real.log 3) ∧
    0 < hausdorffMeasure_value (Real.log 2 / Real.log 3) (cantorSet (1 / 3)) ∧
    hausdorffMeasure_value (Real.log 2 / Real.log 3) (cantorSet (1 / 3)) < ⊤

end
end Specs.D13Unified.Ch18.CantorDimension
