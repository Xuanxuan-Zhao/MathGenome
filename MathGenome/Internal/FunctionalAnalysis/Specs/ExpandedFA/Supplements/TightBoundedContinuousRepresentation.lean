import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Independent statement of `fa2:p1:tight-cb-representation`, paper.tex:5934–5998.
The norm on the restriction to a compact set is its supremum of absolute values;
on the empty set it is zero. The functional is only assumed algebraically linear.
-/

noncomputable section

namespace ExpandedFA.Supplements.TightBoundedContinuousRepresentation.Spec

open Set MeasureTheory
open scoped BoundedContinuousFunction ENNReal

universe u

def Positive {X : Type u} [TopologicalSpace X] (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ L f

def CompactTight {X : Type u} [TopologicalSpace X]
    (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧
    ∀ f : X →ᵇ ℝ,
      |L f| ≤ ‖f.compContinuous ⟨(Subtype.val : K → X), continuous_subtype_val⟩‖ + ε * ‖f‖

def Represents {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (μ : Measure X) : Prop :=
  ∀ f : X →ᵇ ℝ, Integrable f μ ∧ L f = ∫ x, f x ∂μ

def TightProbability {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  μ univ = 1 ∧
  (∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε) ∧
  (∀ A : Set X, MeasurableSet A →
    μ A = ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), μ K)

/-- Existence, probability, tightness, compact inner regularity on every Borel
set, and uniqueness among all finite positive Borel measures. -/
def TightRepresentation : Prop :=
  ∀ (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ),
    Positive L → L 1 = 1 → CompactTight L →
    ∃ μ : Measure X, TightProbability μ ∧ Represents L μ ∧
      ∀ ν : Measure X, IsFiniteMeasure ν → Represents L ν → ν = μ

/-- The uniqueness clause does not require regularity or tightness of the
competing finite measures. -/
def Uniqueness : Prop :=
  ∀ (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (μ ν : Measure X),
    IsFiniteMeasure μ → IsFiniteMeasure ν → Represents L μ → Represents L ν → μ = ν

end ExpandedFA.Supplements.TightBoundedContinuousRepresentation.Spec
