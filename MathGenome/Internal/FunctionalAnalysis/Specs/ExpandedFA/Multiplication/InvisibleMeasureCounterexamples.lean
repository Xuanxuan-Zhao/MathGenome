import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.LpMultiplierSpectrum
import Mathlib.MeasureTheory.Measure.Count

/-! The arbitrary-measure boundary in `fa2:p3:lp-multiplication-compact`,
paper.tex:14162–14205. Finite exponents are essential. The canonical measures
below assign infinite mass to every nonempty set; no semifiniteness is assumed.
The arbitrary-measure domain and transpose interfaces are unchanged. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.Multiplication

/-- Infinite mass at each point. On Unit and ℕ all subsets are measurable. -/
def infiniteCounting (Ω : Type*) [MeasurableSpace Ω] : Measure Ω :=
  (∞ : ℝ≥0∞) • Measure.count

namespace InvisibleMeasureCounterexamplesSpec

def MeasureLaw : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω] (s : Set Ω),
  infiniteCounting Ω s = if s = ∅ then 0 else ∞

/-- In particular both the one-point and natural-number examples have Lp = 0,
over either scalar field, for every positive finite exponent. -/
def FiniteLpZero : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  (p : ℝ≥0∞), p ≠ 0 → p ≠ ∞ →
  ∀ f : Lp 𝕜 p (infiniteCounting Ω), f = 0

/-- All maximal multipliers on a zero Lp space have full domain, are onto,
and have the unique zero-space bounded inverse at every scalar. -/
def ZeroSpaceOperator : Prop := ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)], Subsingleton (Lp 𝕜 p μ) →
  ∀ a : Ω → 𝕜,
  (maximalMultiplier μ p a).domain = ⊤ ∧
  Function.Surjective (maximalMultiplier μ p a).toFun ∧
  (∀ f : (maximalMultiplier μ p a).domain, maximalMultiplier μ p a f = 0) ∧
  Unbounded.OperatorDomainsSpec.resolventSetValue (maximalMultiplier μ p a) = Set.univ

def ZeroSpaceSpectrum : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)], Subsingleton (Lp ℂ p μ) →
  ∀ a : Ω → ℂ, multiplierSpectrum μ p a = ∅

def PointZeroCounterexample : Prop := ∀ {𝕜 : Type*} [RCLike 𝕜]
  (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  Function.Surjective (maximalMultiplier (infiniteCounting Unit) p (fun _ => (0 : 𝕜))).toFun ∧
  ¬ ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂infiniteCounting Unit, c ≤ ‖(0 : Unit → 𝕜) x‖

def PointOneEssentialRange : Prop :=
  multiplierEssentialRange (infiniteCounting Unit) (fun _ => (1 : ℂ)) = {1}

def PointSpectrumResolvent : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ a : Unit → ℂ,
  multiplierSpectrum (infiniteCounting Unit) p a = ∅ ∧
  Unbounded.OperatorDomainsSpec.resolventSetValue
    (maximalMultiplier (infiniteCounting Unit) p a) = Set.univ

/-- The actual unbounded symbol n ↦ n, with its exact maximal domain. -/
def NatFullDomainUnbounded : Prop := ∀ {𝕜 : Type*} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  Measurable (fun n : ℕ => (n : 𝕜)) ∧
  (maximalMultiplier (infiniteCounting ℕ) p (fun n => (n : 𝕜))).domain = ⊤ ∧
  (¬ ∃ C : ℝ, ∀ᵐ (n : ℕ) ∂infiniteCounting ℕ, ‖(n : 𝕜)‖ ≤ C) ∧
  ¬ MemLp (fun n : ℕ => (n : 𝕜)) ∞ (infiniteCounting ℕ)

end InvisibleMeasureCounterexamplesSpec
end ExpandedFA.Multiplication
