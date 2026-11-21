import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.ConvolutionEndpointBounds
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent specifications for paper.tex:17287–17328. The kernel is real,
nonnegative, smooth and compactly supported, with mass one. Its convolution
acts by real scalar multiplication on either manuscript scalar field.
All natural dimensions, including zero, and the endpoint p=1 are retained. -/
set_option autoImplicit false

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.Distributions.SmoothApproximateIdentitiesSpec

abbrev Space (d : ℕ) := Fin d → ℝ

def IsMollifier {d : ℕ} (ρ : Space d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1

def ScaledKernelType := ∀ {d : ℕ}, (Space d → ℝ) → ℝ → Space d → ℝ

def ScaledKernelValue : ScaledKernelType :=
  fun {d} ρ ε x => (ε ^ d)⁻¹ * ρ (ε⁻¹ • x)

def MollifyType := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜],
  (Space d → ℝ) → ℝ → (Space d → 𝕜) → Space d → 𝕜

def MollifyValue : MollifyType := fun ρ ε f =>
  convolution (ScaledKernelValue ρ ε) f (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The rescaling preserves all kernel hypotheses for every positive scale. -/
def ScaledKernelProperties : Prop := ∀ {d : ℕ} (ρ : Space d → ℝ),
  IsMollifier ρ → ∀ ε : ℝ, 0 < ε → IsMollifier (ScaledKernelValue ρ ε)

/-- Convergence in the ordinary Lp space, expressed by its extended norm on
representatives. Each regularized representative belongs to Lp. -/
def LpApproximation : Prop := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
  (ρ : Space d → ℝ), IsMollifier ρ → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
  ∀ f : Space d → 𝕜, MemLp f p volume →
  (∀ ε : ℝ, 0 < ε → MemLp (MollifyValue ρ ε f) p volume) ∧
  Tendsto (fun ε => eLpNorm (MollifyValue ρ ε f - f) p volume)
    (𝓝[>] (0 : ℝ)) (𝓝 0)

def SmoothCompactSupportDense : Prop := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
  (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  Dense {f : Lp 𝕜 p (volume : Measure (Space d)) |
    ∃ g : Space d → 𝕜, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g}

/-- Uniform convergence on each compact set, without global growth assumptions. -/
def LocallyUniformApproximation : Prop := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
  (ρ : Space d → ℝ), IsMollifier ρ → ∀ f : Space d → 𝕜, Continuous f →
  ∀ K : Set (Space d), IsCompact K →
  TendstoUniformlyOn (fun ε => MollifyValue ρ ε f) f (𝓝[>] (0 : ℝ)) K

def UniformApproximation : Prop := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
  (ρ : Space d → ℝ), IsMollifier ρ → ∀ f : Space d → 𝕜, UniformContinuous f →
  TendstoUniformly (fun ε => MollifyValue ρ ε f) f (𝓝[>] (0 : ℝ))

end ExpandedFA.Distributions.SmoothApproximateIdentitiesSpec
