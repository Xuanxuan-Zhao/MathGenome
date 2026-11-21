import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HahnBanach
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Independent statements for the example at paper.tex:1933–1963.
The exponent is in `ℝ≥0∞` with `0 < p < 1`, hence is a finite positive real.
The underlying vector space is Mathlib's actual `Lp`, with its a.e. quotient.
We specify the metric explicitly rather than using its `p ≥ 1` normed instance.
No finiteness or sigma-finiteness of the measure is imposed. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

universe u v

namespace ExpandedFA.P1.NonlocallyConvexSpec

/-- The extended integral used to construct the metric. -/
def powerEDist {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    (p : ℝ≥0∞) (μ : Measure α) (f g : Lp 𝕜 p μ) : ℝ≥0∞ :=
  ∫⁻ x, ‖f x - g x‖ₑ ^ p.toReal ∂μ

/-- The source's real-valued integral distance. Finiteness is a theorem. -/
def powerDist {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    (p : ℝ≥0∞) (μ : Measure α) (f g : Lp 𝕜 p μ) : ℝ :=
  (powerEDist p μ f g).toReal

/-- Nonatomicity uses measurable positive subsets, not merely null singletons.
This quantification permits arbitrary underlying measurable spaces. -/
def Nonatomic {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet s → 0 < μ s →
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < μ s

/-- Metric construction and its exact integral formula and invariance. -/
def MetricRealization : Prop :=
  ∀ (α 𝕜 : Type*) [MeasurableSpace α] [RCLike 𝕜]
    (μ : Measure α) (p : ℝ≥0∞), 0 < p → p < 1 →
    ∃ m : MetricSpace (Lp 𝕜 p μ),
      (∀ f g, @dist _ m.toDist f g = powerDist p μ f g) ∧
      (∀ f g h : Lp 𝕜 p μ, powerDist p μ (f + h) (g + h) = powerDist p μ f g) ∧
      (∀ f g : Lp 𝕜 p μ, powerDist p μ f g = ∫ x, ‖f x - g x‖ ^ p.toReal ∂μ)

/-- Completeness and the vector topology for the exact metric, regardless of
which metric structure realizes that distance. -/
def CompleteVectorTopology : Prop :=
  ∀ (α 𝕜 : Type*) [MeasurableSpace α] [RCLike 𝕜]
    (μ : Measure α) (p : ℝ≥0∞), 0 < p → p < 1 →
    ∀ m : MetricSpace (Lp 𝕜 p μ),
      (∀ f g, @dist _ m.toDist f g = powerDist p μ f g) →
      letI := m
      CompleteSpace (Lp 𝕜 p μ) ∧ TVS 𝕜 (Lp 𝕜 p μ)

/-- The continuous scalar-linear dual is zero, including a zero measure. -/
def TrivialDual : Prop :=
  ∀ (α 𝕜 : Type*) [MeasurableSpace α] [RCLike 𝕜]
    (μ : Measure α) (p : ℝ≥0∞), 0 < p → p < 1 → Nonatomic μ →
    ∀ m : MetricSpace (Lp 𝕜 p μ),
      (∀ f g, @dist _ m.toDist f g = powerDist p μ f g) →
      letI := m
      ∀ ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜, ℓ = 0

/-- We exclude even a topology induced by one seminorm (`IsNormableSpace`),
and thus in particular exclude every compatible norm on the original module. -/
def NonconvexAndNonnormable : Prop :=
  ∀ (α 𝕜 : Type*) [MeasurableSpace α] [RCLike 𝕜]
    (μ : Measure α) (p : ℝ≥0∞), 0 < p → p < 1 → Nonatomic μ →
    ∀ m : MetricSpace (Lp 𝕜 p μ),
      (∀ f g, @dist _ m.toDist f g = powerDist p μ f g) →
      letI := m
      Nontrivial (Lp 𝕜 p μ) →
      ¬ LocallyConvexSpace ℝ (Lp 𝕜 p μ) ∧
      ¬ IsNormableSpace 𝕜 (Lp 𝕜 p μ)

/-- Equal-mass finite decompositions. This is an intermediate measure-theory
obligation, not an assumption of the original example. -/
def EqualMassDecompositions {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ (f : Lp 𝕜 p μ) (n : ℕ), 0 < n →
    ∃ g : Fin n → Lp 𝕜 p μ, (∑ i, g i) = f ∧
      ∀ i, powerDist p μ (g i) 0 ≤ powerDist p μ f 0 / n

/-- The analytic part of the dual proof, separated from nonatomic divisibility. -/
def DualFromDecompositions : Prop :=
  ∀ (α 𝕜 : Type*) [MeasurableSpace α] [RCLike 𝕜]
    (μ : Measure α) (p : ℝ≥0∞), 0 < p → p < 1 →
    EqualMassDecompositions (𝕜 := 𝕜) p μ →
    ∀ m : MetricSpace (Lp 𝕜 p μ),
      (∀ f g, @dist _ m.toDist f g = powerDist p μ f g) →
      letI := m
      ∀ ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜, ℓ = 0

/-- The Hahn–Banach implication used for the final consequences. -/
def NonconvexFromTrivialDual : Prop := TrivialDual.{u, v} → NonconvexAndNonnormable.{u, v}

end ExpandedFA.P1.NonlocallyConvexSpec
