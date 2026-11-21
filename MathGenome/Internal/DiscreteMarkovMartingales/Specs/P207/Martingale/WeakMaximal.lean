import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

/-- The maximum over all times from zero through `n`, including when `n = 0`. -/
noncomputable def finiteMax {Ω : Type u} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => X k ω)

/-- Only the data through the finite horizon are constrained. Values after `n`
are arbitrary; in particular no infinite extension is assumed. -/
def IsSubmartingaleUpTo {Ω : Type u} [m : MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m) (μ : Measure Ω) (n : ℕ) : Prop :=
  (∀ k, k ≤ n → Measurable[ℱ k] (X k)) ∧
  (∀ k, k ≤ n → Integrable (X k) μ) ∧
  ∀ k, k < n → X k ≤ᵐ[μ] μ[X (k + 1) | ℱ k]

namespace WeakMaximalSpec

def constant_extension : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ),
    IsSubmartingaleUpTo X ℱ μ n →
      IsSubmartingale (fun k => X (min k n)) ℱ μ

/-- Signed, localized weak maximal inequality and the positive-part upper bound. -/
def weak_maximal : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ),
    IsSubmartingaleUpTo X ℱ μ n → ∀ (ε : ℝ), 0 < ε →
      ε * (μ {ω | ε ≤ finiteMax X n ω}).toReal ≤
        (∫ ω in {ω | ε ≤ finiteMax X n ω}, X n ω ∂μ) ∧
      (∫ ω in {ω | ε ≤ finiteMax X n ω}, X n ω ∂μ) ≤
        ∫ ω, max (X n ω) 0 ∂μ

/-- The nonnegative case of the same localized estimate. -/
def weak_maximal_nonnegative : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ),
    IsSubmartingaleUpTo X ℱ μ n → (∀ k, k ≤ n → 0 ≤ᵐ[μ] X k) →
    ∀ (ε : ℝ), 0 < ε →
      ε * (μ {ω | ε ≤ finiteMax X n ω}).toReal ≤
        (∫ ω in {ω | ε ≤ finiteMax X n ω}, X n ω ∂μ) ∧
      (∫ ω in {ω | ε ≤ finiteMax X n ω}, X n ω ∂μ) ≤ ∫ ω, X n ω ∂μ

end WeakMaximalSpec
end P207
