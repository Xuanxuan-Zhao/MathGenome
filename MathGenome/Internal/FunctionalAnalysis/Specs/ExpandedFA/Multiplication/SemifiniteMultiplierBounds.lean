import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.MaximalLpMultiplier
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The ordinary essential-bound tests, `fa2:p3:lp-multiplication-bounds`,
paper.tex:14013–14069. No nonzero-space hypothesis is imposed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.Multiplication

/-- Semifiniteness in the precise finite-positive-subset sense of the source. -/
def Semifinite {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  ∀ E : Set Ω, MeasurableSet E → 0 < μ E →
    ∃ F : Set Ω, F ⊆ E ∧ MeasurableSet F ∧ 0 < μ F ∧ μ F < ∞

namespace SemifiniteMultiplierBoundsSpec

/-- The full maximal domain is equivalent to ordinary essential boundedness. -/
def FullDomain : Prop :=
  ∀ {Ω : Type*} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω), Semifinite μ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ a : Ω → 𝕜, Measurable a →
    ((maximalMultiplier μ p a).domain = ⊤ ↔ MemLp a ∞ μ)

/-- When the maximal domain is all of Lp, the operator has a bounded
realization whose norm equals the ordinary L-infinity norm. -/
def NormEquality : Prop :=
  ∀ {Ω : Type*} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω), Semifinite μ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ a : Ω → 𝕜, Measurable a → (maximalMultiplier μ p a).domain = ⊤ →
    ∃ T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ,
      (∀ f : Lp 𝕜 p μ, (T f : Ω → 𝕜) =ᵐ[μ] fun x => a x * f x) ∧
      ‖T‖ = (eLpNorm a ∞ μ).toReal

/-- Closedness of the unclosed maximal range. The lower bound applies only
off the zero level, including when that supported Lp space is zero. -/
def ClosedRange : Prop :=
  ∀ {Ω : Type*} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω), Semifinite μ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ a : Ω → 𝕜, Measurable a →
    (IsClosed ((maximalMultiplier μ p a).toFun.range : Set (Lp 𝕜 p μ)) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂μ, a x ≠ 0 → c ≤ ‖a x‖)

/-- Surjectivity is equivalent to the lower bound everywhere a.e. -/
def Surjectivity : Prop :=
  ∀ {Ω : Type*} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω), Semifinite μ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ a : Ω → 𝕜, Measurable a →
    (Function.Surjective (maximalMultiplier μ p a).toFun ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂μ, c ≤ ‖a x‖)

/-- The everywhere inverse is the reciprocal multiplier, bounded in the
ambient norm, with values in the exact maximal domain and both inverse laws. -/
def BoundedInverse : Prop :=
  ∀ {Ω : Type*} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω), Semifinite μ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ a : Ω → 𝕜, Measurable a → Function.Surjective (maximalMultiplier μ p a).toFun →
    Function.Injective (maximalMultiplier μ p a).toFun ∧
    ∃ B : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ,
      (∀ h : Lp 𝕜 p μ, (B h : Ω → 𝕜) =ᵐ[μ] fun x => (a x)⁻¹ * h x) ∧
      ∃ hB : ∀ h, B h ∈ (maximalMultiplier μ p a).domain,
        (∀ h, maximalMultiplier μ p a ⟨B h, hB h⟩ = h) ∧
        (∀ f : (maximalMultiplier μ p a).domain, B (maximalMultiplier μ p a f) = f)

end SemifiniteMultiplierBoundsSpec
end ExpandedFA.Multiplication
