import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.MaximalLpMultiplier
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpDuality
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.MeasureTheory.Function.L2Space

/-! Exact transpose and adjoint statements for fa2:p3:lp-multiplication.
The positive measure is arbitrary; p is strictly between one and infinity.
The Banach identification is the fixed scalar-linear bilinear integral map.
Equality of Hilbert operators includes their full maximal domains. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
universe u
namespace ExpandedFA.Multiplication.MultiplierTransposeSpec
open FunctionSpaces.ScalarLpIntegralPairingSpec Unbounded

def BanachGraph : Prop :=
  ∀ {Ω : Type u} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], 1 < p → p ≠ ∞ →
    ∀ (a : Ω → 𝕜), Measurable a → ∀ g h : Lp 𝕜 q μ,
    (IntegralPairingValue μ p q g, IntegralPairingValue μ p q h) ∈
      (BanachAdjointSpec.adjointValue (maximalMultiplier μ p a)).graph ↔
    (g, h) ∈ (maximalMultiplier μ q a).graph

def BanachDomain : Prop :=
  ∀ {Ω : Type u} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], 1 < p → p ≠ ∞ →
    ∀ (a : Ω → 𝕜), Measurable a → ∀ g : Lp 𝕜 q μ,
    IntegralPairingValue μ p q g ∈
      (BanachAdjointSpec.adjointValue (maximalMultiplier μ p a)).domain ↔
    MemLp (fun x => a x * g x) q μ

def BanachApply : Prop :=
  ∀ {Ω : Type u} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], 1 < p → p ≠ ∞ →
    ∀ (a : Ω → 𝕜), Measurable a →
    ∀ (g : (maximalMultiplier μ q a).domain)
      (hg : IntegralPairingValue μ p q (g : Lp 𝕜 q μ) ∈
        (BanachAdjointSpec.adjointValue (maximalMultiplier μ p a)).domain),
    BanachAdjointSpec.adjointValue (maximalMultiplier μ p a)
      ⟨IntegralPairingValue μ p q (g : Lp 𝕜 q μ), hg⟩ =
      IntegralPairingValue μ p q (maximalMultiplier μ q a g)

def HilbertAdjoint : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (a : Ω → ℂ),
    Measurable a → HilbertAdjointSpec.adjointValue (maximalMultiplier μ 2 a) =
      maximalMultiplier μ 2 (fun x => conj (a x))

/-- This includes every real-valued multiplier, and is invariant under null changes. -/
def RealSelfAdjoint : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (a : Ω → ℂ),
    Measurable a → (∀ᵐ x ∂μ, (a x).im = 0) →
      IsSelfAdjoint (maximalMultiplier μ 2 a)

end ExpandedFA.Multiplication.MultiplierTransposeSpec
