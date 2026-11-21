import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.RegularShrinking
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-! Independent specification of paper.tex:4467–4499. The input measures
are Borel measures; the density and exceptional set use the canonical completed
Lebesgue space. The density is any finite real measurable representative.
Integrability is a conclusion, not an additional assumption. Ratios are real
ratios; positivity and finiteness of cube volumes are included explicitly.

The cube conclusion allows all Euclidean isometries, hence in particular every
axis-parallel cube (translations of the coordinate cube). All filtered families
are quantified after the exceptional set, so that this set is independent of
the chosen cubes, their positions, and their side lengths. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u

namespace D11.Ch13.MeasureDifferentiation
open D11.Ch03 Specs.D11.Ch03.LebesgueMeasures

/-- Borel Lebesgue decomposition, expressed on Borel sets with a completed
measurable density. Null modifications of the density are allowed. -/
def DensityDecomposition {n : ℕ} [NeZero n]
    (ν σ : Measure (Point n)) (g : Point n → ℝ) : Prop :=
  @Measurable (Point n) ℝ (lebesgueSpace_value n) inferInstance g ∧
  (∀ᵐ x ∂lebesgue_value n, 0 ≤ g x) ∧
  σ ⟂ₘ borelMeasure_value n ∧
  ∀ E : Set (Point n), MeasurableSet E →
    ν E = (∫⁻ y in E, ENNReal.ofReal (g y) ∂lebesgue_value n) + σ E

/-- Scalar ratio. The theorems use it only on sets of finite positive volume
and for finite measures. -/
def measureRatio {n : ℕ} [NeZero n] (ν : Measure (Point n))
    (E : Set (Point n)) : ℝ :=
  (ν E).toReal / (lebesgue_value n E).toReal

/-- One point works for every shrinking family of nondegenerate closed cubes.
This is stronger than the axis-parallel specialization in the source. -/
def CubeLimit {n : ℕ} [NeZero n] (ν : Measure (Point n))
    (a : ℝ) (x : Point n) : Prop :=
  ∀ {ι : Type u} (l : Filter ι) (e : ι → Point n ≃ᵢ Point n) (s : ι → ℝ),
    (∀ i, 0 < s i) →
    (∀ i, x ∈ D11.Ch13.RegularShrinking.closedCube (e i) (s i)) →
    Tendsto s l (𝓝 0) →
    (∀ i, 0 < lebesgue_value n (D11.Ch13.RegularShrinking.closedCube (e i) (s i)) ∧
      lebesgue_value n (D11.Ch13.RegularShrinking.closedCube (e i) (s i)) < ∞) ∧
    Tendsto (fun i => measureRatio ν (D11.Ch13.RegularShrinking.closedCube (e i) (s i)))
      l (𝓝 a)
end D11.Ch13.MeasureDifferentiation

namespace Specs.D11.Ch13.MeasureDifferentiation
open _root_.D11.Ch03 _root_.D11.Ch13.MeasureDifferentiation
open Specs.D11.Ch03.LebesgueMeasures

/-- The independent singular-measure step, for centered open balls. -/
def singular_centered_balls : Prop :=
  ∀ {n : ℕ} [NeZero n] (σ : Measure (Point n)) [IsFiniteMeasure σ],
    σ ⟂ₘ borelMeasure_value n →
    ∀ᵐ x ∂lebesgue_value n,
      Tendsto (fun r => measureRatio σ (Metric.ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Existence of a finite real representative of the Borel decomposition. -/
def exists_density_decomposition : Prop :=
  ∀ {n : ℕ} [NeZero n] (ν : Measure (Point n)) [IsFiniteMeasure ν],
    ∃ (g : Point n → ℝ) (σ : Measure (Point n)),
      DensityDecomposition ν σ g ∧ Integrable g (lebesgue_value n)

/-- Full differentiation for every chosen measurable representative of every
Borel Lebesgue decomposition; no singular ratio conclusion is assumed. -/
def measure_differentiation : Prop :=
  ∀ {n : ℕ} [NeZero n] (ν : Measure (Point n)) [IsFiniteMeasure ν]
    (g : Point n → ℝ) (σ : Measure (Point n)),
    DensityDecomposition ν σ g →
    Integrable g (lebesgue_value n) ∧
    ∃ N : Set (Point n), MeasurableSet[lebesgueSpace_value n] N ∧ lebesgue_value n N = 0 ∧
      ∀ x ∉ N,
        Tendsto (fun r => measureRatio σ (Metric.ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        CubeLimit.{u} σ 0 x ∧ CubeLimit.{u} ν (g x) x
end Specs.D11.Ch13.MeasureDifferentiation
