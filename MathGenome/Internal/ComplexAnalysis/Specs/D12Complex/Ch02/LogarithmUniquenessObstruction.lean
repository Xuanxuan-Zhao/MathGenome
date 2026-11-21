import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Exponential

/-!
The two purely continuous assertions of paper.tex:435–438 (D12.02.04).
`X` has its subspace topology; preconnectedness allows the empty case.
The exponential is the shared factorial-series function `D12Complex.E`.
-/

namespace Specs.D12Complex.Ch02.LogarithmUniquenessObstruction

open _root_.D12Complex

/-- Two continuous logarithms on a connected subset differ by one fixed
integral multiple of 2πi. Neither openness nor holomorphy is required. -/
def continuous_logarithms_difference_type : Prop :=
  ∀ (X : Set ℂ), IsPreconnected X →
    ∀ (f L₁ L₂ : X → ℂ), (∀ x, f x ≠ 0) →
      Continuous L₁ → Continuous L₂ →
      (∀ x, E (L₁ x) = f x) → (∀ x, E (L₂ x) = f x) →
      ∃ k : ℤ, ∀ x, L₁ x - L₂ x = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ)

/-- There is no continuous right inverse of E on the punctured plane. -/
def no_continuous_logarithm_type : Prop :=
  ¬ ∃ L : {z : ℂ // z ≠ 0} → ℂ,
    Continuous L ∧ ∀ z, E (L z) = (z : ℂ)

end Specs.D12Complex.Ch02.LogarithmUniquenessObstruction
