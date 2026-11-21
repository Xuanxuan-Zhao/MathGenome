import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent specifications for the circle part of paper.tex:5992–5998.
The measure is on exactly the Borel sigma-algebra of the concrete unit circle.
It is arc length, with total mass `2 * π`, rather than Haar probability. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch21.CircleHaarExample

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

def arcLength_type := @Measure Circle (borel Circle)

def arcLength_value : @Measure Circle (borel Circle) :=
  Measure.map Circle.exp (volume.restrict (Ico 0 (2 * Real.pi)))

def arcLength_apply : Prop :=
  ∀ E : Set Circle, MeasurableSet[borel Circle] E →
    arcLength_value E = volume (Circle.exp ⁻¹' E ∩ Ico 0 (2 * Real.pi))

def arcLength_mass : Prop :=
  arcLength_value univ = ENNReal.ofReal (2 * Real.pi)

def arcLength_finite_nonzero : Prop :=
  arcLength_value ≠ 0 ∧ arcLength_value univ < ∞

def arcLength_radon : Prop :=
  Specs.D11.Ch18.RadonPredicates.isRadonValue arcLength_value

def rotation_invariant : Prop :=
  ∀ (a : Circle) (E : Set Circle), MeasurableSet[borel Circle] E →
    arcLength_value ((fun x => a * x) '' E) = arcLength_value E

def right_rotation_invariant : Prop :=
  ∀ (a : Circle) (E : Set Circle), MeasurableSet[borel Circle] E →
    arcLength_value ((fun x => x * a) '' E) = arcLength_value E

def arcLength_two_sided_haar : Prop :=
  Specs.D11.Ch21.HaarDefinition.leftHaarValue arcLength_value ∧
    Specs.D11.Ch21.HaarDefinition.rightHaarValue arcLength_value

end Specs.D11.Ch21.CircleHaarExample
