import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveContentOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates

/-!
Independent statements for the Radon conclusion and the two exact estimates in
paper.tex:5526–5530, within `d11:19:positive-content-measure`.

All objects are the canonical ones from the preceding construction. The measure
has exactly the Borel domain; no countability or total-mass bound is imposed.
`ofReal` embeds the nonnegative functional values into `[0,∞]`, so the inequalities
also make sense when the mass on the other side is infinite. The first estimate
quantifies over arbitrary subsets, without requiring Borel measurability.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch19.PositiveContentRadon
universe u

open Specs.D11.Ch19.PositiveContentOuterMeasure

/-- The Chapter 18 Radon predicate, with precisely its three regularity conditions. -/
def radon : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I),
    Specs.D11.Ch18.RadonPredicates.isRadonValue (borelMeasure_value I hI)

/-- Exact outer-mass bound from a nonnegative compactly supported majorant of one. -/
def outerMeasure_le_functional : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (A : Set X) (h : CompactlySupportedContinuousMap X ℝ),
    (∀ x, 0 ≤ h x) → (∀ x ∈ A, 1 ≤ h x) →
      outerMeasure_value I hI A ≤ ENNReal.ofReal (I h)

/-- Exact lower bound on compact masses from nonnegative tests bounded by one. -/
def functional_le_compact_measure : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (K : Set X), IsCompact K →
    ∀ f : CompactlySupportedContinuousMap X ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) → closure {x | f x ≠ 0} ⊆ K →
        ENNReal.ofReal (I f) ≤ borelMeasure_value I hI K

end Specs.D11.Ch19.PositiveContentRadon
