import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvOneSided
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Normed.Group.Real

/-! Independent statements for the positive part of paper.tex:3915–3929.
The measurable space on ℝ is its Borel space. All measures below are positive;
real evaluations use `Measure.real`, with finiteness explicitly required.
Boundedness, right continuity and normalization are hypotheses, not conclusions
hidden in a certificate for the measure to be constructed. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Specs.D11.Ch12.PositiveStieltjes

abbrev positiveGenerator_type := (ℝ → ℝ) → Prop

def positiveGenerator_value : positiveGenerator_type := fun F =>
  Monotone F ∧ (∀ x, ContinuousWithinAt F (Ici x) x) ∧
    Tendsto F atBot (𝓝 0) ∧ ∃ C : ℝ, ∀ x, |F x| ≤ C

abbrev stieltjesMeasure_type :=
  (F : ℝ → ℝ) → positiveGenerator_value F → Measure ℝ

noncomputable def stieltjesMeasure_value : stieltjesMeasure_type := fun F h =>
  (StieltjesFunction.mk F h.1 h.2.1).measure

abbrev cumulative_type := Measure ℝ → ℝ → ℝ

noncomputable def cumulative_value : cumulative_type := fun μ x => μ.real (Iic x)

def finite_type : Prop :=
  ∀ (F : ℝ → ℝ) (h : positiveGenerator_value F),
    IsFiniteMeasure (stieltjesMeasure_value F h)

def interval_type : Prop :=
  ∀ (F : ℝ → ℝ) (h : positiveGenerator_value F) {a b : ℝ}, a < b →
    stieltjesMeasure_value F h (Ioc a b) = ENNReal.ofReal (F b - F a)

def cumulative_measure_type : Prop :=
  ∀ (F : ℝ → ℝ) (h : positiveGenerator_value F) (x : ℝ),
    cumulative_value (stieltjesMeasure_value F h) x = F x

def initial_interval_type : Prop :=
  ∀ (F : ℝ → ℝ) (h : positiveGenerator_value F) (x : ℝ),
    stieltjesMeasure_value F h (Iic x) = ENNReal.ofReal (F x)

def atom_type : Prop :=
  ∀ (F : ℝ → ℝ) (h : positiveGenerator_value F) (x : ℝ),
    stieltjesMeasure_value F h {x} = ENNReal.ofReal (F x - Function.leftLim F x)

def atom_real_type : Prop :=
  ∀ (F : ℝ → ℝ) (h : positiveGenerator_value F) (x : ℝ),
    (stieltjesMeasure_value F h).real {x} = F x - Function.leftLim F x

def left_limit_type : Prop :=
  ∀ (F : ℝ → ℝ) (h : positiveGenerator_value F) (x : ℝ),
    Tendsto F (𝓝[<] x) (𝓝 (Function.leftLim F x))

def unique_type : Prop :=
  ∀ (F : ℝ → ℝ) (h : positiveGenerator_value F) (ν : Measure ℝ),
    IsFiniteMeasure ν →
    (∀ a b : ℝ, a < b → ν (Ioc a b) = ENNReal.ofReal (F b - F a)) →
    ν = stieltjesMeasure_value F h

def cumulative_properties_type : Prop :=
  ∀ (μ : Measure ℝ), IsFiniteMeasure μ → positiveGenerator_value (cumulative_value μ)

def measure_cumulative_type : Prop :=
  ∀ (μ : Measure ℝ), IsFiniteMeasure μ →
    ∀ h : positiveGenerator_value (cumulative_value μ),
      stieltjesMeasure_value (cumulative_value μ) h = μ

def global_bv_type : Prop :=
  ∀ (F : ℝ → ℝ), positiveGenerator_value F → Specs.D11.Ch12.GloballyBV_value F

def existence_uniqueness_type : Prop :=
  ∀ (F : ℝ → ℝ), positiveGenerator_value F →
    ∃! ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ a b : ℝ, a < b → ν (Ioc a b) = ENNReal.ofReal (F b - F a)

end Specs.D11.Ch12.PositiveStieltjes
