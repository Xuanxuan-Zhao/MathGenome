import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Independent statements for the weighted estimate in paper.tex:14500–14526.
The Fourier convention here is the native negative 2πi convention. Thus the
resolvent is evaluated at ξ + 2πis, which parametrizes the same vertical line.
No separability assumption is imposed on the Hilbert space.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace ExpandedFA.Semigroups.WeightedResolvent
open Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Local W¹,², with its distributional derivative.
Tests are real scalar smooth compactly supported functions; the equality is in H.
No pointwise differentiability or continuity of the chosen representative is
assumed. In particular this permits continuous piecewise C¹ curves. -/
def LocalW12 (w dw : ℝ → H) : Prop :=
  (∀ a b : ℝ, MemLp w 2 (volume.restrict (Set.Icc a b))) ∧
  (∀ a b : ℝ, MemLp dw 2 (volume.restrict (Set.Icc a b))) ∧
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ t, deriv φ t • w t) = -(∫ t, φ t • dw t)

def weighted (ξ : ℝ) (w : ℝ → H) (t : ℝ) : H := Real.exp (-ξ * t) • w t

def energy (ξ : ℝ) (w : ℝ → H) : ℝ :=
  ∫ t, ‖w t‖ ^ 2 * Real.exp (-2 * ξ * t)

/-- An H-valued residual with the exact domain of the partial operator. -/
def residual (G : Operator ℂ H H) (w dw : ℝ → H)
    (hD : ∀ t, w t ∈ G.domain) (t : ℝ) : H := dw t - G ⟨w t, hD t⟩

def LineBound (G : Operator ℂ H H) (ξ d : ℝ) : Prop :=
  0 < d ∧ ∀ τ : ℝ,
    (ξ + Complex.I * τ : ℂ) ∈ OperatorDomainsSpec.resolventSetValue G ∧
    ‖OperatorDomainsSpec.resolventValue (ξ + Complex.I * τ) G‖ ≤ 1 / d

namespace Spec

def HilbertIntegralAgreement : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (f : ℝ → H) (_h1 : Integrable f)
    (h2 : MemLp f 2),
  (Lp.fourierTransformₗᵢ ℝ H (h2.toLp f) : ℝ → H) =ᵐ[volume] 𝓕 f

def HilbertIntegralPlancherel : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (f : ℝ → H),
  Integrable f → MemLp f 2 →
    MemLp (𝓕 f) 2 ∧ (∫ s, ‖𝓕 f s‖ ^ 2) = ∫ t, ‖f t‖ ^ 2

def IntegralGraph : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (G : Operator ℂ H H), G.IsClosed →
  ∀ (w : ℝ → H) (hD : ∀ t, w t ∈ G.domain),
  Integrable w → Integrable (fun t => G ⟨w t, hD t⟩) →
  ∃ h : (∫ t, w t) ∈ G.domain, G ⟨∫ t, w t, h⟩ = ∫ t, G ⟨w t, hD t⟩

def FourierGraph : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (G : Operator ℂ H H), G.IsClosed →
  ∀ (w : ℝ → H) (hD : ∀ t, w t ∈ G.domain),
  Integrable w → Integrable (fun t => G ⟨w t, hD t⟩) →
  ∀ s : ℝ, ∃ h : 𝓕 w s ∈ G.domain,
    G ⟨𝓕 w s, h⟩ = 𝓕 (fun t => G ⟨w t, hD t⟩) s

def ResolventLowerBound : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (G : Operator ℂ H H) (ξ d : ℝ),
  LineBound G ξ d → ∀ (τ : ℝ) (x : G.domain),
    d * ‖(x : H)‖ ≤ ‖(ξ + Complex.I * τ : ℂ) • (x : H) - G x‖

/-- The analytic multiplier step, separately from establishing its Fourier
identity for weakly differentiable curves. -/
def FourierCoercivity : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (G : Operator ℂ H H) (ξ d : ℝ),
  LineBound G ξ d → ∀ (f r : ℝ → H),
  Integrable f → MemLp f 2 → Integrable r → MemLp r 2 →
  (∀ s : ℝ, ∃ h : 𝓕 f s ∈ G.domain,
    𝓕 r s = (ξ + Complex.I * (2 * Real.pi * s) : ℂ) • 𝓕 f s - G ⟨𝓕 f s, h⟩) →
  d ^ 2 * (∫ t, ‖f t‖ ^ 2) ≤ ∫ t, ‖r t‖ ^ 2

def WeightedEnergy : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (ξ : ℝ) (w : ℝ → H),
  (∫ t, ‖weighted ξ w t‖ ^ 2) = energy ξ w

/-- The compact-support estimate. Only Gw, rather than w in the graph topology,
is required to be square integrable. The derivative is a weak derivative. -/
def CompactEstimate : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (G : Operator ℂ H H),
  G.IsClosed → Dense (G.domain : Set H) → ∀ (ξ d : ℝ),
  LineBound G ξ d → ∀ (w dw : ℝ → H) (hD : ∀ t, w t ∈ G.domain),
  LocalW12 w dw → HasCompactSupport w →
  MemLp (fun t => G ⟨w t, hD t⟩) 2 →
  d ^ 2 * energy ξ w ≤ energy ξ (residual G w dw hD)

/-- Extension to locally graph-continuous curves by smooth cutoffs, retaining
the weak derivative interpretation and both weighted L² assumptions. -/
def CutoffEstimate : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (G : Operator ℂ H H),
  G.IsClosed → Dense (G.domain : Set H) → ∀ (ξ d : ℝ),
  LineBound G ξ d → ∀ (w dw : ℝ → H) (hD : ∀ t, w t ∈ G.domain),
  LocalW12 w dw → Continuous w → Continuous (fun t => G ⟨w t, hD t⟩) →
  MemLp (weighted ξ w) 2 → MemLp (weighted ξ (residual G w dw hD)) 2 →
  d ^ 2 * energy ξ w ≤ energy ξ (residual G w dw hD)

end Spec
end ExpandedFA.Semigroups.WeightedResolvent
