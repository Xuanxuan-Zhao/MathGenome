import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.CompactCutoff
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Measure.Support

/-!
Independent specifications for paper.tex:5418–5426.
The sigma-algebra is exactly Borel. The null-open union is an arbitrary set
union, not a countable union. Real Cc maps with values in [0,1] represent
precisely the source's Cc(X,[0,1]) tests. Their scalar integrability is a
separate conclusion, so the integral characterization does not rely on the
value of a totalized integral for nonintegrable maps.
-/
namespace Specs.D11.Ch18.RadonSupport

open Set MeasureTheory
universe u

local instance {Y : Type u} [TopologicalSpace Y] : MeasurableSpace Y := borel Y

/-- Canonical union of all open null sets, with no countability restriction. -/
def nullOpenUnionValue {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) : Set X :=
  ⋃₀ {U : Set X | IsOpen U ∧ μ U = 0}

/-- Canonical source support, the complement of the null-open union. -/
def supportValue {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) : Set X :=
  (nullOpenUnionValue μ)ᶜ

def setType :=
  ∀ {X : Type u} [TopologicalSpace X], @Measure X (borel X) → Set X

def nullOpenUnion_isOpen : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    IsOpen (nullOpenUnionValue μ)

def nullOpenUnion_null : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonPredicates.isRadonValue μ →
    μ (nullOpenUnionValue μ) = 0

def support_eq_measureSupport : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    supportValue μ = μ.support

def support_isClosed : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    IsClosed (supportValue μ)

def cc_integrable : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonPredicates.isRadonValue μ →
    ∀ f : CompactlySupportedContinuousMap X ℝ,
      Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value μ (fun x => f x)

def mem_support_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonPredicates.isRadonValue μ → ∀ x : X,
    x ∈ supportValue μ ↔
      ∀ f : CompactlySupportedContinuousMap X ℝ,
        (∀ y, 0 ≤ f y ∧ f y ≤ 1) → 0 < f x → 0 < ∫ y, f y ∂μ

end Specs.D11.Ch18.RadonSupport
