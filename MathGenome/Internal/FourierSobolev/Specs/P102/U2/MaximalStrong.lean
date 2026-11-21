import MathGenome.Internal.FourierSobolev.Specs.P102.U2.MaximalWeak
import MathGenome.Internal.FourierSobolev.Specs.P102.U2.Marcinkiewicz

/-! Strong maximal estimates, paper.tex:912–918. The Boolean selects the
uncentered operator when true and the centered operator when false. All
integrals use the same completed Lebesgue measure as the upstream definitions.
Extended moments retain infinite values until a.e. finiteness is proved. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace P102.U2.MaximalStrongSpec
open D11.Ch03
open Specs.P102.U2.MaximalWeak
open ExpandedFA.Interpolation.MarcinkiewiczSpec
local instance (d : ℕ) [NeZero d] : MeasurableSpace (Point d) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value d

variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]

def maximalValue (uncentered : Bool) (f : Point d → 𝕜) : Point d → ℝ≥0∞ :=
  if uncentered then uncentered_value f else centered_value f

def LocalIntegrability : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (p : ℝ≥0∞), 1 ≤ p → ∀ f : Point d → 𝕜, MemLp f p (μ d) → LocalL1 f

def SumDomainLocal : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point d → 𝕜), sumDomain (μ d) 1 ∞ f → LocalL1 f

/-- Sublinearity of the extended maximal action, on its whole local domain
and hence on L¹ + L∞. Congruence is pointwise equality of maximal functions. -/
def SublinearAction : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (b : Bool) (f : Point d → 𝕜), LocalL1 f →
    Measurable (maximalValue b f) ∧
    (∀ g, LocalL1 g → f =ᵐ[μ d] g → maximalValue b f = maximalValue b g) ∧
    (∀ g, LocalL1 g → ∀ x,
      maximalValue b (f + g) x ≤ maximalValue b f x + maximalValue b g x) ∧
    (∀ c : 𝕜, ∀ x, maximalValue b (c • f) x =
      ENNReal.ofReal ‖c‖ * maximalValue b f x)

/-- The constant is uniform over scalar fields, inputs and the two operators.
Both the extended moment norm and the ordinary Lp representative are bounded. -/
def FiniteStrongBound : Prop :=
  ∀ (d : ℕ) [NeZero d] (p : ℝ), 1 < p → ∃ C : ℝ≥0,
    ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
      (b : Bool) (f : Point d → 𝕜), MemLp f (ENNReal.ofReal p) (μ d) →
      (∫⁻ x, maximalValue b f x ^ p ∂(μ d)) ^ (1 / p) ≤
        (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (μ d) ∧
      (∀ᵐ x ∂(μ d), maximalValue b f x < ∞) ∧
      MemLp (fun x => (maximalValue b f x).toReal) (ENNReal.ofReal p) (μ d) ∧
      eLpNorm (fun x => (maximalValue b f x).toReal) (ENNReal.ofReal p) (μ d) ≤
        (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (μ d)

def InfinityStrongBound : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (b : Bool) (f : Point d → 𝕜), MemLp f ∞ (μ d) →
    (∀ x, maximalValue b f x ≤ eLpNorm f ∞ (μ d)) ∧
      essSup (maximalValue b f) (μ d) ≤ eLpNorm f ∞ (μ d)
end P102.U2.MaximalStrongSpec
