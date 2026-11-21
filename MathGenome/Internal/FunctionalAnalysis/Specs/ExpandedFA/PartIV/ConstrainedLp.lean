import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpIntegralPairing

/-! Ordinary real Lp classes on an arbitrary positive measure. No measure-size
hypothesis is imposed. The exponent q is the Hölder conjugate p'.
Source: paper.tex, fa2:p4:constrained-support, the interior Lp assertion. -/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace ExpandedFA.PartIV.ConstrainedLp.Spec

def IntervalSupport : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    1 < p → p ≠ ∞ → ∀ k : Lp ℝ q μ, (∀ᵐ x ∂μ, 0 ≤ k x) →
    ∀ u : Lp ℝ p μ,
    (∀ g : Lp ℝ q μ, (∀ᵐ x ∂μ, |g x| ≤ k x) →
      (∫ x, u x * g x ∂μ) ≤ ∫ x, k x * |u x| ∂μ) ∧
    ∃ g : Lp ℝ q μ, (∀ᵐ x ∂μ, |g x| ≤ k x) ∧
      (∫ x, u x * g x ∂μ) = ∫ x, k x * |u x| ∂μ

def KernelAnnihilator : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    1 < p → p ≠ ∞ → ∀ j h : Lp ℝ q μ,
    (∀ u : Lp ℝ p μ, (∫ x, u x * j x ∂μ) = 0 →
      (∫ x, u x * h x ∂μ) = 0) ↔ ∃ c : ℝ, h = c • j

def ConstrainedEquivalence : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    1 < p → p ≠ ∞ → ∀ f j k : Lp ℝ q μ,
    (∀ᵐ x ∂μ, 0 ≤ k x) →
    ((∀ u : Lp ℝ p μ, (∫ x, u x * j x ∂μ) = 0 →
        (∫ x, u x * f x ∂μ) ≤ ∫ x, k x * |u x| ∂μ) ↔
      ∃ (c : ℝ) (g : Lp ℝ q μ), f = c • j + g ∧
        ∀ᵐ x ∂μ, |g x| ≤ k x)
end ExpandedFA.PartIV.ConstrainedLp.Spec
