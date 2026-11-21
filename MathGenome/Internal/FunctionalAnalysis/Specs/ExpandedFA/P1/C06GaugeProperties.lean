import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Gauge
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05Sublinear
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Complex.Basic

/-! Independent statements for paper.tex:1048–1081 (`fa2:p1:c06:gauge-properties`). The gauge and admissibility
are the upstream specification formulas. No separation or completeness axiom is used. -/
namespace Specs.ExpandedFA.P1.C06GaugeProperties
open ExpandedFA.P1.C06GaugeSpec
open scoped Topology Pointwise
universe u v

/-- Finiteness means a genuine real GLB, with a finite positive upper bound
coming from an actual dilation, rather than the fallback infimum of an empty set. -/
def finiteType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (U : Set E),
    admissibleValue U → ∀ x : E,
    IsGLB (scalesValue U x) (gaugeValue U x) ∧
      ∃ t : ℝ, 0 < t ∧ x ∈ t • U ∧ gaugeValue U x ≤ t

def nonnegType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (U : Set E),
    admissibleValue U → ∀ x : E, 0 ≤ gaugeValue U x

def zeroType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (U : Set E),
    admissibleValue U → gaugeValue U 0 = 0

def homogeneousType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (U : Set E),
    admissibleValue U → ∀ t : ℝ, 0 ≤ t → ∀ x : E,
      gaugeValue U (t • x) = t * gaugeValue U x

def subadditiveType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (U : Set E),
    admissibleValue U → ∀ x y : E, gaugeValue U (x + y) ≤ gaugeValue U x + gaugeValue U y

def sublinearType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (U : Set E),
    admissibleValue U → Specs.ExpandedFA.P1.C05Sublinear.isSublinearValue (gaugeValue U)

def openUnitType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (U : Set E),
    Convex ℝ U → (0 : E) ∈ U → IsOpen U → U = {x | gaugeValue U x < 1}

def dominatedContinuousType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (U : Set E),
    Convex ℝ U → (0 : E) ∈ U → IsOpen U → ∀ h : E →ₗ[ℝ] ℝ,
      (∀ x, h x ≤ gaugeValue U x) → Continuous h

/-- The stronger continuity statement holds without balance. -/
def continuousType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (U : Set E),
    Convex ℝ U → (0 : E) ∈ U → IsOpen U → Continuous (gaugeValue U)

/-- `RCLike` includes both ℝ and ℂ. The real action is compatible with scalar
restriction. This states both the continuous seminorm representation and its
absolute scalar homogeneity, including the zero scalar. -/
def continuousSeminormType : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜] {E : Type u} [AddCommGroup E]
    [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [ContinuousSMul 𝕜 E] (U : Set E),
    Convex ℝ U → (0 : E) ∈ U → IsOpen U → Balanced 𝕜 U →
    (∃ p : Seminorm 𝕜 E, (∀ x, p x = gaugeValue U x) ∧ Continuous (p : E → ℝ)) ∧
      (∀ a : 𝕜, ∀ x : E, gaugeValue U (a • x) = ‖a‖ * gaugeValue U x)

/-- Specialization to an arbitrary complex TVS; its real action is the
canonical one, with no extra real-topology hypothesis. -/
def complexContinuousSeminormType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (U : Set E), Convex ℝ U → (0 : E) ∈ U → IsOpen U → Balanced ℂ U →
    (∃ p : Seminorm ℂ E, (∀ x, p x = gaugeValue U x) ∧ Continuous (p : E → ℝ)) ∧
      (∀ a : ℂ, ∀ x : E, gaugeValue U (a • x) = ‖a‖ * gaugeValue U x)

/-- No openness or balance is needed for this quantitative bound. -/
def normBoundType : Prop :=
  ∀ {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (r : ℝ), 0 < r → Metric.ball (0 : E) r ⊆ U →
      ∀ x : E, gaugeValue U x ≤ ‖x‖ / r

/-- The complex normed formulation uses the canonical restriction to ℝ. -/
def complexNormBoundType : Prop :=
  ∀ {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℂ E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    ∀ (U : Set E) (r : ℝ), 0 < r → Metric.ball (0 : E) r ⊆ U →
      ∀ x : E, gaugeValue U x ≤ ‖x‖ / r

end Specs.ExpandedFA.P1.C06GaugeProperties
