import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.SemifiniteMultiplierBounds
import Mathlib.Analysis.Complex.Basic

/-! Spectrum clauses of `fa2:p3:lp-multiplication-spectrum`, paper.tex:14071–14100.
The real endpoint and continuous-symbol clauses are assigned separately.
The spectrum uses the accepted two-sided bounded ambient inverse definition,
so this includes unbounded maximal operators and the zero space. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.Multiplication

/-- Ordinary essential range, using strictly positive measure of every ball. -/
def multiplierEssentialRange {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a : Ω → ℂ) : Set ℂ :=
  {z | ∀ ε : ℝ, 0 < ε → 0 < μ {x | ‖a x - z‖ < ε}}

/-- Spectrum of the exact domain-carrying maximal operator. -/
def multiplierSpectrum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Ω → ℂ) : Set ℂ :=
  (Unbounded.OperatorDomainsSpec.resolventSetValue (maximalMultiplier μ p a))ᶜ

/-- Ambient eigenspace: membership includes membership in the maximal domain. -/
def multiplierEigenspace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) (a : Ω → ℂ) (z : ℂ) :
    Submodule ℂ (Lp ℂ p μ) :=
  (Unbounded.OperatorDomainsSpec.shiftValue z (maximalMultiplier μ p a)).ker

namespace LpMultiplierSpectrumSpec

def EssentialRangeClosed : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (a : Ω → ℂ), IsClosed (multiplierEssentialRange μ a)

def SpectrumFormula : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω), Semifinite μ →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  ∀ a : Ω → ℂ, Measurable a →
  multiplierSpectrum μ p a = multiplierEssentialRange μ a

def ResolventFormula : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω), Semifinite μ →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  ∀ a : Ω → ℂ, Measurable a → ∀ z : ℂ,
  z ∉ multiplierEssentialRange μ a →
  (∀ f : Lp ℂ p μ,
    (Unbounded.OperatorDomainsSpec.resolventValue z (maximalMultiplier μ p a) f : Ω → ℂ)
      =ᵐ[μ] fun x => f x / (z - a x)) ∧
  ‖Unbounded.OperatorDomainsSpec.resolventValue z (maximalMultiplier μ p a)‖ =
    (eLpNorm (fun x => (z - a x)⁻¹) ∞ μ).toReal

def EigenspaceFormula : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Ω → ℂ) (z : ℂ),
  multiplierEigenspace μ p a z = supportedLp μ p {x | a x = z}

def EigenvalueFormula : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω), Semifinite μ →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  ∀ a : Ω → ℂ, Measurable a → ∀ z : ℂ,
  (∃ f : (maximalMultiplier μ p a).domain,
    (f : Lp ℂ p μ) ≠ 0 ∧ maximalMultiplier μ p a f = z • (f : Lp ℂ p μ)) ↔
    0 < μ {x | a x = z}

/-- Complex Lp itself is the complexification of real Lp. -/
def AmbientComplexification : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  (∀ f : Lp ℂ p μ,
    (f : Ω → ℂ) =ᵐ[μ] fun x => (Complex.reCLM.compLp f x : ℂ) +
      Complex.I * (Complex.imCLM.compLp f x : ℂ)) ∧
  (∀ u v : Lp ℝ p μ, ∃ f : Lp ℂ p μ,
    (f : Ω → ℂ) =ᵐ[μ] (fun x => (u x : ℂ) + Complex.I * (v x : ℂ)) ∧
    Complex.reCLM.compLp f = u ∧ Complex.imCLM.compLp f = v)

/-- Exact domain decomposition and agreement of the operator with its real
and imaginary parts. No essential boundedness of the real symbol is assumed. -/
def RealComplexification : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Ω → ℝ),
  (∀ f : Lp ℂ p μ,
    f ∈ (maximalMultiplier μ p (fun x => (a x : ℂ))).domain ↔
    ∃ u v : (maximalMultiplier μ p a).domain,
      (f : Ω → ℂ) =ᵐ[μ] fun x => ((u : Lp ℝ p μ) x : ℂ) +
        Complex.I * ((v : Lp ℝ p μ) x : ℂ)) ∧
  (∀ (f : (maximalMultiplier μ p (fun x => (a x : ℂ))).domain)
     (u v : (maximalMultiplier μ p a).domain),
    ((f : Lp ℂ p μ) : Ω → ℂ) =ᵐ[μ] (fun x => ((u : Lp ℝ p μ) x : ℂ) +
        Complex.I * ((v : Lp ℝ p μ) x : ℂ)) →
    (maximalMultiplier μ p (fun x => (a x : ℂ)) f : Ω → ℂ) =ᵐ[μ]
      fun x => (maximalMultiplier μ p a u x : ℂ) +
        Complex.I * (maximalMultiplier μ p a v x : ℂ))

def RealSpectrumFormula : Prop := ∀ {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω), Semifinite μ →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
  ∀ a : Ω → ℝ, Measurable a →
  multiplierSpectrum μ p (fun x => (a x : ℂ)) =
    multiplierEssentialRange μ (fun x => (a x : ℂ))

end LpMultiplierSpectrumSpec
end ExpandedFA.Multiplication
