import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.SemifiniteMultiplierBounds
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.MeasureTheory.Measure.Count

/-! The compactness assertions of `fa2:p3:lp-multiplication-compact`.
The chapter assumes 1 < p < ∞, over either scalar field. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.Multiplication

/-- A measure has no atoms: every measurable positive set splits into two
measurable pieces of positive measure. This is stronger than null singletons. -/
def Nonatomic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  ∀ E : Set Ω, MeasurableSet E → 0 < μ E →
    ∃ F : Set Ω, F ⊆ E ∧ MeasurableSet F ∧ 0 < μ F ∧ 0 < μ (E \ F)

/-- Image of the ambient closed unit ball intersected with the exact domain. -/
def multiplierUnitImage {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Ω → 𝕜) : Set (Lp 𝕜 p μ) :=
  (maximalMultiplier μ p a) '' {f | ‖(f : Lp 𝕜 p μ)‖ ≤ 1}

namespace NonatomicMultiplierNoncompactnessSpec

def Noncompactness : Prop :=
  ∀ {Ω : Type*} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω), Semifinite μ → Nonatomic μ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ a : Ω → 𝕜, Measurable a → ¬ (a =ᵐ[μ] 0) →
      ¬ IsCompact (closure (multiplierUnitImage μ p a))

/-- Any continuous linear realization of the everywhere-defined multiplier. -/
def CompactIffZero : Prop :=
  ∀ {Ω : Type*} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω), Semifinite μ → Nonatomic μ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (a : Ω → 𝕜), Measurable a →
    ∀ T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ,
      (∀ f, (T f : Ω → 𝕜) =ᵐ[μ] fun x => a x * f x) →
      (IsCompactOperator T ↔ a =ᵐ[μ] 0)

/-- Counting measure on the natural numbers. Index n represents manuscript
coordinate n+1, so the multiplier is 1/(n+1). Its truncation keeps n < m. -/
def CountingExample : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ (T : Lp 𝕜 p (Measure.count : Measure ℕ) →L[𝕜] Lp 𝕜 p Measure.count)
      (S : ℕ → Lp 𝕜 p Measure.count →L[𝕜] Lp 𝕜 p Measure.count),
      (∀ f, (T f : ℕ → 𝕜) =ᵐ[Measure.count]
        fun n => ((n : 𝕜) + 1)⁻¹ * f n) ∧
      T ≠ 0 ∧ IsCompactOperator T ∧
      (∀ m, (∀ f, (S m f : ℕ → 𝕜) =ᵐ[Measure.count]
          fun n => if n < m then ((n : 𝕜) + 1)⁻¹ * f n else 0) ∧
        FiniteDimensional 𝕜 (S m).toLinearMap.range ∧
        ‖T - S m‖ = 1 / ((m : ℝ) + 1))

end NonatomicMultiplierNoncompactnessSpec
end ExpandedFA.Multiplication
