import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.LyapunovPurification
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Independent statements for `paper.tex:23389–23419`, `fa2:p5:lyapunov`.
Ranges use ordinary measurable sets. Nonatomicity is atomlessness of the
variation, or a finite atomless control measure dominating all coordinate
variations. Convexity is over ℝ, also for complex targets. No positive-dimension,
nonzero-measure, separability, or completeness-of-the-measurable-space assumption
is imposed. Finite-dimensional vector measures are represented by their finite
list of signed coordinates; the final statements also use native vector measures.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v

namespace ExpandedFA.PartV.Lyapunov.Spec

/-- The actual range on measurable sets, without values on nonmeasurable sets. -/
def measurableRange {X E : Type*} [MeasurableSpace X] (m : Set X → E) : Set E :=
  {b | ∃ s : Set X, MeasurableSet s ∧ m s = b}

/-- The weak-star order interval, in the usual a.e. quotient. -/
def densityInterval {X : Type u} [MeasurableSpace X] (μ : Measure X) :
    Set (Lp ℝ ∞ μ) := {g | ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1}

/-- Integrable coordinates define the finite-dimensional moment map. -/
def momentMap {X : Type u} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (h : Fin n → X → ℝ) (g : Lp ℝ ∞ μ) : Fin n → ℝ :=
  fun j => ∫ x, g x * h j x ∂μ

def MomentImageCompactConvex : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {n : ℕ} (h : Fin n → X → ℝ), (∀ j, Integrable (h j) μ) →
    IsCompact (momentMap μ h '' densityInterval μ) ∧
      Convex ℝ (momentMap μ h '' densityInterval μ)

def RangeEqualsMomentImage : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ],
    LyapunovPurification.Spec.Atomless μ →
    ∀ {n : ℕ} (h : Fin n → X → ℝ), (∀ j, Integrable (h j) μ) →
    measurableRange (fun s => fun j => ∫ x in s, h j x ∂μ) =
      momentMap μ h '' densityInterval μ

/-- The coordinate version includes the Radon–Nikodym bridge and exact image
identity, rather than presupposing that a vector measure already has densities. -/
def CoordinateLyapunov : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ],
    LyapunovPurification.Spec.Atomless μ →
    ∀ {n : ℕ} (m : Fin n → SignedMeasure X),
    (∀ j, (m j).totalVariation ≪ μ) →
    ∃ h : Fin n → X → ℝ, (∀ j, Integrable (h j) μ) ∧
      (∀ s : Set X, MeasurableSet s → ∀ j, m j s = ∫ x in s, h j x ∂μ) ∧
      measurableRange (fun s => fun j => m j s) =
        momentMap μ h '' densityInterval μ ∧
      IsCompact (measurableRange (fun s => fun j => m j s)) ∧
      Convex ℝ (measurableRange (fun s => fun j => m j s))

/-- Coordinate-free control-measure formulation. Absolute continuity of the
vector measure implies domination of each coordinate variation. -/
def DominatedLyapunov : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure X) [IsFiniteMeasure μ], LyapunovPurification.Spec.Atomless μ →
    ∀ m : VectorMeasure X E, m ≪ᵥ μ.toENNRealVectorMeasure →
    IsCompact (measurableRange m) ∧ Convex ℝ (measurableRange m)

/-- Finite vector measures with atomless total variation. -/
def FiniteDimensionalLyapunov : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (m : VectorMeasure X E) [IsFiniteMeasure m.variation],
    LyapunovPurification.Spec.Atomless m.variation →
    IsCompact (measurableRange m) ∧ Convex ℝ (measurableRange m)

/-- Complex dimension n is handled as real dimension 2n. -/
def ComplexLyapunov : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {n : ℕ}
    (m : VectorMeasure X (Fin n → ℂ)) [IsFiniteMeasure m.variation],
    LyapunovPurification.Spec.Atomless m.variation →
    IsCompact (measurableRange m) ∧ Convex ℝ (measurableRange m)

end ExpandedFA.PartV.Lyapunov.Spec
