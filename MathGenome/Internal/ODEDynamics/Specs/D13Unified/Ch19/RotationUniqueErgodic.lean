import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.CircleLift
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.NumberTheory.Real.Irrational

/-! Independent specification of the invariant-probability uniqueness clause of
`paper.tex`, Theorem `d13:19:rotation-ergodicity`. The measure is the actual
Lebesgue measure descended from a fundamental interval of length one. -/
namespace Specs.D13Unified.Ch19.RotationUniqueErgodic

noncomputable section
open MeasureTheory Set
open Specs.D13Unified.Ch15

abbrev Circle := CircleLift.Circle

def rotationType := ℝ → Circle → Circle
def rotation : rotationType := fun α x => x + CircleLift.quotientMap α

def lebesgueProbabilityType := Measure Circle
def lebesgueProbability : lebesgueProbabilityType := volume

def rotation_quotientStatement : Prop :=
  ∀ α x : ℝ, rotation α (CircleLift.quotientMap x) = CircleLift.quotientMap (x + α)

/-- A pushforward of ordinary real Lebesgue measure, restricted to a unit interval. -/
def lebesgueProbability_eq_mapStatement : Prop :=
  ∀ t : ℝ, lebesgueProbability =
    Measure.map CircleLift.quotientMap (volume.restrict (Ioc t (t + 1)))

def lebesgueProbability_isProbabilityStatement : Prop :=
  IsProbabilityMeasure lebesgueProbability

/-- In particular, integration has precisely the source's normalization. -/
def integral_lebesgueProbabilityStatement : Prop :=
  ∀ f : Circle → ℝ, (∫ x, f x ∂lebesgueProbability) =
    ∫ t in (0 : ℝ)..1, f (CircleLift.quotientMap t)

def rotation_preserves_lebesgueProbabilityStatement : Prop :=
  ∀ α : ℝ, MeasureDefinitions.PreservesMeasure (rotation α) lebesgueProbability

/-- No regularity or absolute-continuity assumption is imposed on the candidate
Borel probability; the measurable space is the canonical Borel space on ℝ/ℤ. -/
def invariant_probability_uniqueStatement : Prop :=
  ∀ α : ℝ, Irrational α → ∀ η : Measure Circle, IsProbabilityMeasure η →
    MeasureDefinitions.PreservesMeasure (rotation α) η → η = lebesgueProbability

end
end Specs.D13Unified.Ch19.RotationUniqueErgodic
