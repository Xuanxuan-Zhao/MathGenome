import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import Mathlib.Topology.Semicontinuity.Basic

/-! Independent statements for paper.tex:4449–4465. `Point d` carries the
Euclidean norm. The input measure is on the Borel sigma-algebra; the volume
in the denominator and in the estimate is the completed Lebesgue measure.
The supremum takes all positive real radii, with extended nonnegative values.
Zero measures are admitted. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch13.MeasureWeakBound
open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures

def maximal_type := (d : ℕ) → [NeZero d] → Measure (Point d) → Point d → ℝ≥0∞

def maximal_value : maximal_type := fun d _ μ x =>
  ⨆ (r : ℝ) (_ : 0 < r), μ (Metric.ball x r) / lebesgue_value d (Metric.ball x r)

def fixed_radius_lowerSemicontinuous : Prop :=
  ∀ (d : ℕ) [NeZero d] (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (r : ℝ), 0 < r → LowerSemicontinuous (fun x => μ (Metric.ball x r))

def maximal_lowerSemicontinuous : Prop :=
  ∀ (d : ℕ) [NeZero d] (μ : Measure (Point d)) [IsFiniteMeasure μ],
    LowerSemicontinuous (maximal_value d μ)

def maximal_measurable : Prop :=
  ∀ (d : ℕ) [NeZero d] (μ : Measure (Point d)) [IsFiniteMeasure μ],
    Measurable (maximal_value d μ) ∧
      @Measurable (Point d) ℝ≥0∞ (lebesgueSpace_value d) inferInstance (maximal_value d μ)

def measure_weak_bound : Prop :=
  ∀ (d : ℕ) [NeZero d] (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (α : ℝ), 0 < α →
    lebesgue_value d {x | ENNReal.ofReal α < maximal_value d μ x} ≤
      (3 : ℝ≥0∞) ^ d * μ Set.univ / ENNReal.ofReal α
end Specs.D11.Ch13.MeasureWeakBound
