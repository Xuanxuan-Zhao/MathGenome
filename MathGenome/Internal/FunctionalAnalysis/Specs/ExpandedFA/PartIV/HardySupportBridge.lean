import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyExponentialFactor

/-! `fa2:p4:titchmarsh`, first paragraph of the proof (paper.tex 18978–18994).
Support is essential support, so null sets and representatives do not affect it.
`IsLeftEndpoint` specifies the lower endpoint by all its lower support bounds.
The positive-exponential Fourier–Laplace convention is inherited unchanged. -/
noncomputable section
open MeasureTheory Set
namespace ExpandedFA.PartIV.HardySupportBridge
open HardyHalfPlaneRepresentationSpec HardyExponentialFactor

def SupportedAbove (f : ℝ → ℂ) (c : ℝ) : Prop :=
  ∀ᵐ t ∂(volume : Measure ℝ), t < c → f t = 0

def IsLeftEndpoint (f : ℝ → ℂ) (a : ℝ) : Prop :=
  ∀ c : ℝ, SupportedAbove f c ↔ c ≤ a

def translate (f : ℝ → ℂ) (b : ℝ) : ℝ → ℂ := fun t => f (t + b)

def convolution (f g : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t, f t * g (x - t)

namespace Spec

def ExponentialThreshold : Prop := ∀ F : ℂ → ℂ, IsH2 F →
  ∀ a : ℝ, HasCoefficient F a → ∀ b : ℝ, 0 ≤ b →
  (IsH2 (fun z => exponentialInner (-b) z * F z) ↔ b ≤ a)

def SupportCriterion : Prop := ∀ f : ℝ → ℂ, MemLp f 2 volume →
  SupportedAbove f 0 → ∀ c : ℝ, 0 ≤ c →
  (SupportedAbove f c ↔
    IsH2 (fun z => exponentialInner (-(2 * Real.pi * c)) z * laplace f z))

/-- The arbitrary initial lower bound is retained, and the actual translated
transform is used. Nonzero means nonzero in L², rather than at an isolated point. -/
def EndpointCoefficient : Prop := ∀ f : ℝ → ℂ, MemLp f 2 volume →
  ¬ (f =ᵐ[volume] 0) → ∀ b : ℝ, SupportedAbove f b →
  ∃ a : ℝ, 0 ≤ a ∧ HasCoefficient (laplace (translate f b)) a ∧
    IsLeftEndpoint f (b + a / (2 * Real.pi))

/-- Every choice of the distinguished coefficient gives the same endpoint. -/
def EndpointOfCoefficient : Prop := ∀ f : ℝ → ℂ, MemLp f 2 volume →
  ∀ b : ℝ, SupportedAbove f b → ∀ a : ℝ,
  HasCoefficient (laplace (translate f b)) a →
    0 ≤ a ∧ IsLeftEndpoint f (b + a / (2 * Real.pi))

def ConvolutionEndpoints : Prop := ∀ f g : ℝ → ℂ,
  Integrable f → Integrable g → MemLp f 2 volume → MemLp g 2 volume →
  ¬ (f =ᵐ[volume] 0) → ¬ (g =ᵐ[volume] 0) →
  (∃ b, SupportedAbove f b) → (∃ b, SupportedAbove g b) →
  MemLp (convolution f g) 2 volume ∧ ¬ (convolution f g =ᵐ[volume] 0) ∧
    ∃ a b : ℝ, IsLeftEndpoint f a ∧ IsLeftEndpoint g b ∧
      IsLeftEndpoint (convolution f g) (a + b)

/-- The addition identity for any specified lower endpoints. -/
def EndpointAddition : Prop := ∀ f g : ℝ → ℂ,
  Integrable f → Integrable g → MemLp f 2 volume → MemLp g 2 volume →
  ¬ (f =ᵐ[volume] 0) → ¬ (g =ᵐ[volume] 0) →
  ∀ a b : ℝ, IsLeftEndpoint f a → IsLeftEndpoint g b →
  MemLp (convolution f g) 2 volume ∧ ¬ (convolution f g =ᵐ[volume] 0) ∧
    IsLeftEndpoint (convolution f g) (a + b)

end Spec
end ExpandedFA.PartIV.HardySupportBridge
