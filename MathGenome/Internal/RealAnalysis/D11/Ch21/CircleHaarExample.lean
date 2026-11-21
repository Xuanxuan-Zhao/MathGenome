import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch18.SecondCountableBorelRegular
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CircleHaarExample
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Arc length on the unit circle, paper.tex:5992–5998.
The half-open interval is the source interval `[0,2π)` exactly. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace D11.Ch21.CircleHaarExample

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Arc length is the specified pushforward of restricted real Lebesgue measure. -/
def arcLength : @Measure Circle (borel Circle) :=
  Measure.map Circle.exp (volume.restrict (Ico 0 (2 * Real.pi)))

theorem arcLength_apply (E : Set Circle) (hE : MeasurableSet[borel Circle] E) :
    arcLength E = volume (Circle.exp ⁻¹' E ∩ Ico 0 (2 * Real.pi)) := by
  rw [arcLength, Measure.map_apply Circle.exp.continuous.measurable hE,
    Measure.restrict_apply (Circle.exp.continuous.measurable hE)]

theorem arcLength_mass : arcLength univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [arcLength_apply univ MeasurableSet.univ]
  simp

theorem arcLength_finite_nonzero : arcLength ≠ 0 ∧ arcLength univ < ∞ := by
  constructor
  · intro h
    have hm := arcLength_mass
    rw [h] at hm
    have hp : ¬ Real.pi ≤ 0 := not_le.mpr Real.pi_pos
    exact hp (by simpa using hm)
  · rw [arcLength_mass]
    exact ENNReal.ofReal_lt_top

instance : IsFiniteMeasure arcLength := ⟨arcLength_finite_nonzero.2⟩

theorem arcLength_radon : D11.Ch18.isRadon arcLength := by
  exact (D11.Ch18.SecondCountableBorelRegular.second_countable_regular arcLength
    (fun K _ => measure_lt_top arcLength K)).2.1

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Endpoint changes affect only two Lebesgue-null singletons. This connects the
source's `[0,2π)` to the library's fundamental domain `(0,2π]`. -/
theorem arcLength_eq_map_addCircle :
    arcLength = Measure.map AddCircle.homeomorphCircle'
      (volume : Measure (AddCircle (2 * Real.pi))) := by
  rw [← (AddCircle.measurePreserving_mk (2 * Real.pi) 0).map_eq]
  rw [Measure.map_map AddCircle.homeomorphCircle'.continuous.measurable
    AddCircle.measurable_mk']
  have he : (volume : Measure ℝ).restrict (Ico 0 (2 * Real.pi)) =
      volume.restrict (Ioc 0 (0 + 2 * Real.pi)) := by
    simpa using Measure.restrict_congr_set
      (Ico_ae_eq_Ioc' (measure_singleton (0 : ℝ)) (measure_singleton (2 * Real.pi)))
  rw [arcLength, he]
  rfl

private theorem homeomorphCircle'_add (x y : AddCircle (2 * Real.pi)) :
    AddCircle.homeomorphCircle' (x + y) =
      AddCircle.homeomorphCircle' x * AddCircle.homeomorphCircle' y := by
  induction x using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  exact Circle.exp_add _ _

instance : IsMulLeftInvariant arcLength where
  map_mul_left_eq_self a := by
    obtain ⟨u, rfl⟩ := AddCircle.homeomorphCircle'.surjective a
    rw [arcLength_eq_map_addCircle,
      Measure.map_map (measurable_const_mul _) AddCircle.homeomorphCircle'.continuous.measurable]
    have hc : (fun x : Circle => AddCircle.homeomorphCircle' u * x) ∘
        AddCircle.homeomorphCircle' =
        AddCircle.homeomorphCircle' ∘ (fun x => u + x) := by
      funext x
      exact (homeomorphCircle'_add u x).symm
    rw [hc, ← Measure.map_map AddCircle.homeomorphCircle'.continuous.measurable
      (measurable_const_add u), map_add_left_eq_self]

theorem rotation_invariant (a : Circle) (E : Set Circle)
    (_hE : MeasurableSet[borel Circle] E) :
    arcLength ((fun x => a * x) '' E) = arcLength E := by
  rw [Set.image_mul_left, measure_preimage_mul]

theorem right_rotation_invariant (a : Circle) (E : Set Circle)
    (hE : MeasurableSet[borel Circle] E) :
    arcLength ((fun x => x * a) '' E) = arcLength E := by
  simpa only [mul_comm] using rotation_invariant a E hE

theorem arcLength_two_sided_haar :
    D11.Ch21.isLeftHaarMeasure arcLength ∧ D11.Ch21.isRightHaarMeasure arcLength := by
  exact ⟨⟨arcLength_finite_nonzero.1, arcLength_radon, rotation_invariant⟩,
    ⟨arcLength_finite_nonzero.1, arcLength_radon, right_rotation_invariant⟩⟩

end D11.Ch21.CircleHaarExample
