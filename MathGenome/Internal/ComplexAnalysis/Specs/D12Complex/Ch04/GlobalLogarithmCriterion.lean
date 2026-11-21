import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Exponential
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PrimitivePeriodCriterion

/-! The logarithm assertions of paper.tex:1163–1194 (D12.04.07).
All functions are total representatives restricted to the stated domain.
The exponential is the shared factorial-series exponential, and periods use
all canonical piecewise C1 paths on arbitrary compact parameter intervals.
There is no simple-connectivity assumption. -/
noncomputable section
namespace Specs.D12Complex.Ch04.GlobalLogarithmCriterion
open _root_.D12Complex

/-- Local Cauchy regularity makes the actual logarithmic derivative holomorphic. -/
def holomorphicOn_logarithmicDerivative_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f →
    (∀ z ∈ Ω, f z ≠ 0) → HolomorphicOn Ω (fun z => deriv f z / f z)

/-- Every holomorphic logarithm has derivative f′/f at every domain point. -/
def logarithm_hasDerivAt_type : Prop :=
  ∀ (Ω : Set ℂ) (f L : ℂ → ℂ), HolomorphicOn Ω f → HolomorphicOn Ω L →
    (∀ z ∈ Ω, f z ≠ 0) → (∀ z ∈ Ω, E (L z) = f z) →
    ∀ z ∈ Ω, HasDerivAt L (deriv f z / f z) z

/-- Existence is equivalent to vanishing along every closed piecewise C1 path. -/
def global_logarithm_criterion_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω f →
    (∀ z ∈ Ω, f z ≠ 0) →
    ((∃ L : ℂ → ℂ, HolomorphicOn Ω L ∧ ∀ z ∈ Ω, E (L z) = f z) ↔
      ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed →
        γ.integral (fun z => deriv f z / f z) = 0)

/-- The integer is one constant for the whole domain. -/
def holomorphic_logarithms_difference_type : Prop :=
  ∀ (Ω : Set ℂ) (f L₁ L₂ : ℂ → ℂ), IsDomain Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
    HolomorphicOn Ω L₁ → HolomorphicOn Ω L₂ →
    (∀ z ∈ Ω, E (L₁ z) = f z) → (∀ z ∈ Ω, E (L₂ z) = f z) →
    ∃ k : ℤ, ∀ z ∈ Ω,
      L₁ z - L₂ z = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ)

end Specs.D12Complex.Ch04.GlobalLogarithmCriterion
