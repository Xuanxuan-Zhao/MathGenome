import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ConvexEnergySubendpoint
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Independent statement of the counterexample in `fa2:p4:nemytskii-energy`,
paper.tex:21501–21520. The measure is Lebesgue measure on (0,1), and all
functions and continuous linear tests are real. The exponent ranges over
all 1 < p < infinity. The primitive, upper growth, conjugate exponent and
weak convergence are exactly the upstream objects.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.ConvexEnergyCounterexample.Spec

open ConvexEnergySubendpoint.Spec

/-- Lebesgue measure on the original open unit interval. -/
def unitIntervalMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsFiniteMeasure unitIntervalMeasure := by
  unfold unitIntervalMeasure
  infer_instance

/-- The support used by the source's concentrated sequence. -/
abbrev spikeSet (p : ℝ≥0∞) (a : ℝ) : Set ℝ := Ioo 0 (a ^ (-p.toReal))

/-- Native ordinary-a.e. Lp class of a constant on the shrinking support. -/
def spike (p : ℝ≥0∞) (a : ℝ) : Lp ℝ p unitIntervalMeasure :=
  indicatorConstLp p (s := spikeSet p a) measurableSet_Ioo (measure_ne_top _ _) a

/-- Scalar ramp data sufficient for the example. This is an obligation to
construct actual functions and amplitudes, not an assumed certificate. -/
def RampConstruction : Prop :=
  ∀ (p : ℝ≥0∞), 1 < p → p ≠ ∞ →
  ∃ (g₀ : ℝ → ℝ) (a : ℕ → ℝ),
    Continuous g₀ ∧ Monotone g₀ ∧ UpperGrowth p g₀ ∧ g₀ 0 = 0 ∧
    (∀ n, 1 ≤ a n) ∧ Tendsto a atTop atTop ∧
    (∀ n, a n ^ (p.toReal - 1) ≤ g₀ (a n)) ∧
    Tendsto (fun n => a n ^ (-p.toReal) * primitive g₀ (a n)) atTop (𝓝 0)

/-- Full endpoint failure with an actual strictly increasing continuous
nonlinearity. Integrability and image membership are explicit, so neither
integral nor norm failure can be caused by a nonintegrable function. -/
def Counterexample : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  ∃ (g : ℝ → ℝ) (v : ℕ → Lp ℝ p unitIntervalMeasure),
    Continuous g ∧ StrictMono g ∧ UpperGrowth p g ∧ g 0 = 0 ∧
    WeaklyConverges unitIntervalMeasure p v 0 ∧
    (∀ n, Integrable (fun x => primitive g (v n x)) unitIntervalMeasure) ∧
    Tendsto (fun n => ∫ x, primitive g (v n x) ∂unitIntervalMeasure) atTop (𝓝 0) ∧
    (∀ n, ‖v n‖ = 1) ∧
    (∀ n, MemLp (fun x => g (v n x) - g 0) (conjugate p) unitIntervalMeasure) ∧
    (∀ n, 1 ≤ (eLpNorm (fun x => g (v n x) - g 0)
      (conjugate p) unitIntervalMeasure).toReal) ∧
    ¬ Tendsto (fun n => ‖v n‖) atTop (𝓝 0) ∧
    ¬ Tendsto (fun n => (eLpNorm (fun x => g (v n x) - g 0)
      (conjugate p) unitIntervalMeasure).toReal) atTop (𝓝 0)

end ExpandedFA.PartIV.ConvexEnergyCounterexample.Spec
