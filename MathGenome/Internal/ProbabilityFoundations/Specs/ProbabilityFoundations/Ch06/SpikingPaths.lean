import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.Tightness
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The example in paper.tex 2342–2354. `n ≥ 1` is the manuscript's
indexing; sequences of laws are indexed by `n + 1` to start at one.
All path topologies and norms below are the canonical uniform ones. -/

open MeasureTheory Filter Topology Set

namespace ProbabilityFoundations.Ch06.SpikeSpec

noncomputable section

abbrev UnitTime := Set.Icc (0 : ℝ) 1
abbrev RealPath := C(UnitTime, ℝ)

def width (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- A continuous extension of the triangular path to the real line. -/
def tent (n : ℕ) : C(ℝ, ℝ) where
  toFun t := max 0 (min (2 * (t / width n - 1)) (2 * (2 - t / width n)))
  continuous_toFun := continuous_const.max
    ((continuous_const.mul ((continuous_id.div_const _).sub continuous_const)).min
      (continuous_const.mul (continuous_const.sub (continuous_id.div_const _))))

def spikeValue (n : ℕ) : RealPath where
  toFun t := tent n t
  continuous_toFun := (tent n).continuous.comp continuous_subtype_val

def spikeType := ℕ → RealPath

/-- Exact geometry, including both linear halves and both endpoints.
`width n = 2⁻ⁿ`, and `2 * width n = 2^(1-n)` for `n ≥ 1`. -/
def shapeType : Prop := ∀ n : ℕ, 1 ≤ n →
  (∀ t : ℝ, 0 ≤ tent n t ∧ tent n t ≤ 1) ∧
  (∀ t : ℝ, t ≤ width n ∨ 2 * width n ≤ t → tent n t = 0) ∧
  (∀ t : ℝ, width n ≤ t → t ≤ 3 * width n / 2 →
    tent n t = 2 * (t / width n - 1)) ∧
  (∀ t : ℝ, 3 * width n / 2 ≤ t → t ≤ 2 * width n →
    tent n t = 2 * (2 - t / width n)) ∧
  tent n (width n) = 0 ∧ tent n (2 * width n) = 0 ∧
  tent n (3 * width n / 2) = 1

def pointwiseType : Prop := ∀ t : UnitTime,
  Tendsto (fun n : ℕ => spikeValue (n + 1) t) atTop (𝓝 0)

def normType : Prop := ∀ n : ℕ, 1 ≤ n → ‖spikeValue n‖ = 1

/-- Finite-dimensional convergence at every finite collection of times,
including the empty collection and repeated coordinates. -/
def finiteDimensionalType : Prop := ∀ (k : ℕ) (t : Fin k → UnitTime),
  Tendsto (fun n : ℕ =>
    ( _root_.Specs.ProbabilityFoundations.Ch06.Tightness.diracLawValue
      (spikeValue (n + 1))).map (fun x : RealPath => fun i : Fin k => x (t i)))
    atTop (𝓝 (_root_.Specs.ProbabilityFoundations.Ch06.Tightness.diracLawValue
      (fun _ : Fin k => (0 : ℝ))))

/-- The real-valued instance of the manuscript's modulus. -/
def realIncrements (x : RealPath) (δ : ℝ) : Set ℝ :=
  {r | ∃ s t : UnitTime, |(s : ℝ) - (t : ℝ)| ≤ δ ∧ r = ‖x s - x t‖}

def realModulus (x : RealPath) (δ : ℝ) : ℝ := sSup (realIncrements x δ)

def modulusType : Prop := ∀ δ : ℝ, 0 < δ →
  ∀ᶠ n : ℕ in atTop, realModulus (spikeValue (n + 1)) δ = 1

def notTightType : Prop :=
  ¬ _root_.Specs.ProbabilityFoundations.Ch06.Tightness.uniformlyTightValue
    (range (fun n : ℕ =>
      _root_.Specs.ProbabilityFoundations.Ch06.Tightness.diracLawValue (spikeValue (n + 1))))

/-- This excludes the zero-path law and every other probability law. -/
def noWeakLimitType : Prop := ∀ μ : ProbabilityMeasure RealPath,
  ¬ Tendsto (fun n : ℕ =>
    _root_.Specs.ProbabilityFoundations.Ch06.Tightness.diracLawValue (spikeValue (n + 1)))
    atTop (𝓝 μ)

end
end ProbabilityFoundations.Ch06.SpikeSpec
