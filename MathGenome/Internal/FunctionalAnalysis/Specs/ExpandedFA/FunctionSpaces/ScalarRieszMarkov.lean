import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! Independent statements for the finite scalar part of `fa2:p4:riesz-markov`.
The measurable structure is Borel, the scalar measures are native countably
additive vector measures, and integration pairs by multiplication, without
complex conjugation. No countability or nonemptiness hypothesis is imposed. -/

namespace ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec

open Set MeasureTheory
open scoped ENNReal ZeroAtInfty
universe u

/-- A scalar Radon measure has finite total variation, which satisfies the
paper's explicit three Radon conditions. -/
def FiniteScalarRadon {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (ν : VectorMeasure X 𝕜) : Prop :=
  ν.variation univ < ∞ ∧ PositiveRadonRepresentationSpec.PositiveRadon ν.variation

/-- Scalar measure integration is multiplication of function values and
measure values. In particular this introduces no complex conjugation. -/
noncomputable def scalarIntegral {X : Type u} [MeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜] (ν : VectorMeasure X 𝕜) (f : X → 𝕜) : 𝕜 :=
  ν.integral f (ContinuousLinearMap.mul ℝ 𝕜)

/-- The exact finite scalar Riesz--Markov assertion. Uniqueness is among
all finite Radon scalar measures, not just a chosen construction. -/
def ScalarRepresentation (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (L : C₀(X, 𝕜) →L[𝕜] 𝕜),
    ∃ ν : VectorMeasure X 𝕜,
      FiniteScalarRadon ν ∧
      (∀ f : C₀(X, 𝕜), Integrable f ν.variation ∧ L f = scalarIntegral ν f) ∧
      ‖L‖ = ν.variation.real univ ∧
      ∀ η : VectorMeasure X 𝕜, FiniteScalarRadon η →
        (∀ f : C₀(X, 𝕜), Integrable f η.variation ∧ L f = scalarIntegral η f) → η = ν

def RealRepresentation : Prop := ScalarRepresentation.{u} ℝ

def ComplexRepresentation : Prop := ScalarRepresentation.{u} ℂ

/-- The additional positive bounded-functional assertion in the source proof.
Both integrability and mass equal to operator norm are explicit. -/
def PositiveRepresentation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (L : C₀(X, ℝ) →L[ℝ] ℝ),
    (∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f) →
    ∃ μ : Measure X,
      PositiveRadonRepresentationSpec.PositiveRadon μ ∧ μ univ < ∞ ∧
      (∀ f : C₀(X, ℝ), Integrable f μ ∧ L f = ∫ x, f x ∂μ) ∧
      ‖L‖ = μ.real univ ∧
      ∀ η : Measure X, PositiveRadonRepresentationSpec.PositiveRadon η → η univ < ∞ →
        (∀ f : C₀(X, ℝ), Integrable f η ∧ L f = ∫ x, f x ∂η) → η = μ

/-- Positivity in the complex case means that nonnegative real-valued tests
have nonnegative real functional values. The representing measure is positive,
and the pairing is the ordinary complex Bochner integral. -/
def ComplexPositiveRepresentation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (L : C₀(X, ℂ) →L[ℂ] ℂ),
    (∀ f : C₀(X, ℂ), (∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re) →
      (L f).im = 0 ∧ 0 ≤ (L f).re) →
    ∃ μ : Measure X,
      PositiveRadonRepresentationSpec.PositiveRadon μ ∧ μ univ < ∞ ∧
      (∀ f : C₀(X, ℂ), Integrable f μ ∧ L f = ∫ x, f x ∂μ) ∧
      ‖L‖ = μ.real univ ∧
      ∀ η : Measure X, PositiveRadonRepresentationSpec.PositiveRadon η → η univ < ∞ →
        (∀ f : C₀(X, ℂ), Integrable f η ∧ L f = ∫ x, f x ∂η) → η = μ

/-- The compact identification preserves the actual functions in both
directions and the supremum norm. It includes the empty compact space. -/
def CompactIdentification : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X]
    (𝕜 : Type*) [RCLike 𝕜],
    ∃ e : C(X, 𝕜) ≃ₗᵢ[𝕜] C₀(X, 𝕜),
      (∀ f x, e f x = f x) ∧ (∀ f x, e.symm f x = f x)

/-- Explicit boundary case of the scalar representation assertion. -/
def EmptyRepresentation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsEmpty X]
    (𝕜 : Type) [RCLike 𝕜] (L : C₀(X, 𝕜) →L[𝕜] 𝕜),
    ∃ ν : VectorMeasure X 𝕜,
      FiniteScalarRadon ν ∧
      (∀ f : C₀(X, 𝕜), Integrable f ν.variation ∧ L f = scalarIntegral ν f) ∧
      ‖L‖ = ν.variation.real univ ∧
      ∀ η : VectorMeasure X 𝕜, FiniteScalarRadon η →
        (∀ f : C₀(X, 𝕜), Integrable f η.variation ∧ L f = scalarIntegral η f) → η = ν

end ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
