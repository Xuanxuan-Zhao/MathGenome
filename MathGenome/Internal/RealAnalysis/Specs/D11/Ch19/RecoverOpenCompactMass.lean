import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveRieszMarkov

/-!
Independent statements of paper.tex:5552–5558. All masses, suprema and
infima take values in [0,∞]. In the complex formulas the tests take
nonnegative real values; `re` identifies their real functional values with
ℝ before embedding into ENNReal. Support is the closure of the nonzero set.
The representing measure has exactly the Borel domain and the shared Radon
predicate. No countability or finite-total-mass hypothesis is imposed.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch19.RecoverOpenCompactMass
universe u

open Specs.D11.Ch19.PositiveContentOuterMeasure (Positive)
open Specs.D11.Ch19.PositiveRieszMarkov (Represents ComplexPositive)

def real_open_mass : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ), Positive I →
    ∀ μ : @Measure X (borel X), Represents I μ →
    ∀ U : Set X, IsOpen U →
      μ U = ⨆ f : CompactlySupportedContinuousMap X ℝ,
        ⨆ (_ : ∀ x, 0 ≤ f x ∧ f x ≤ 1),
          ⨆ (_ : closure {x | f x ≠ 0} ⊆ U), ENNReal.ofReal (I f)

def real_compact_mass : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ), Positive I →
    ∀ μ : @Measure X (borel X), Represents I μ →
    ∀ K : Set X, IsCompact K →
      μ K = ⨅ g : CompactlySupportedContinuousMap X ℝ,
        ⨅ (_ : ∀ x, 0 ≤ g x), ⨅ (_ : ∀ x ∈ K, 1 ≤ g x), ENNReal.ofReal (I g)

def complex_open_mass : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ), ComplexPositive I →
    ∀ μ : @Measure X (borel X), Represents I μ →
    ∀ U : Set X, IsOpen U →
      μ U = ⨆ f : CompactlySupportedContinuousMap X ℂ,
        ⨆ (_ : ∀ x, 0 ≤ (f x).re ∧ (f x).re ≤ 1 ∧ (f x).im = 0),
          ⨆ (_ : closure {x | f x ≠ 0} ⊆ U), ENNReal.ofReal (I f).re

def complex_compact_mass : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ), ComplexPositive I →
    ∀ μ : @Measure X (borel X), Represents I μ →
    ∀ K : Set X, IsCompact K →
      μ K = ⨅ g : CompactlySupportedContinuousMap X ℂ,
        ⨅ (_ : ∀ x, 0 ≤ (g x).re ∧ (g x).im = 0),
          ⨅ (_ : ∀ x ∈ K, 1 ≤ (g x).re), ENNReal.ofReal (I g).re

end Specs.D11.Ch19.RecoverOpenCompactMass
