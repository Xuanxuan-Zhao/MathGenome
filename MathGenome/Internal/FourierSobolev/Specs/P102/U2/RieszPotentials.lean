import MathGenome.Internal.FourierSobolev.Specs.P102.U2.MaximalWeak
import MathGenome.Internal.FourierSobolev.Specs.P102.U2.WeakNorms
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Independent scope for Theorem p102:U2-04, paper.tex:978–988.
The domain is Euclidean space with the same completed Lebesgue measure as the
maximal-function interfaces. Scalar fields include both real and complex values.
The Bochner integral is totalized in the usual way; the two bounds separately
require absolute existence almost everywhere. No critical exponent is included. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace P102.U2.RieszPotentialsSpec
open D11.Ch03
abbrev μ (d : ℕ) [NeZero d] := Specs.P102.U2.MaximalWeak.μ d
local instance (d : ℕ) [NeZero d] : MeasurableSpace (Point d) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value d

/-- Unnormalized Riesz kernel. In the asserted parameter range its value at zero
is zero, by the convention for real powers. Changing that value is harmless. -/
def kernelValue {d : ℕ} (α : ℝ) (z : Point d) : ℝ := ‖z‖ ^ (α - (d : ℝ))

def potentialValue {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    (α : ℝ) (f : Point d → 𝕜) (x : Point d) : 𝕜 :=
  ∫ y, kernelValue α (x - y) • f y ∂μ d

/-- Extended absolute integral, retaining divergence. -/
def absoluteValue {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    (α : ℝ) (f : Point d → 𝕜) (x : Point d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (kernelValue α (x - y) * ‖f y‖) ∂μ d

def KernelType := ∀ {d : ℕ}, ℝ → Point d → ℝ
def PotentialType := ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜],
  ℝ → (Point d → 𝕜) → Point d → 𝕜
def AbsoluteType := ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜],
  ℝ → (Point d → 𝕜) → Point d → ℝ≥0∞

def RepresentativeIndependence : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    (α : ℝ) (f g : Point d → 𝕜), f =ᵐ[μ d] g →
    potentialValue α f = potentialValue α g ∧
    absoluteValue α f = absoluteValue α g ∧
    ∀ x, Integrable (fun y => kernelValue α (x-y) • f y) (μ d) ↔
      Integrable (fun y => kernelValue α (x-y) • g y) (μ d)

def Measurability : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (α : ℝ) (f : Point d → 𝕜), AEStronglyMeasurable f (μ d) →
    Measurable (potentialValue α f) ∧ Measurable (absoluteValue α f)

def OriginIndependence : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
    (α : ℝ) (k : Point d → ℝ),
    (∀ z, z ≠ 0 → k z = kernelValue α z) →
    ∀ (f : Point d → 𝕜) (x : Point d),
      (Integrable (fun y => k (x-y) • f y) (μ d) ↔
        Integrable (fun y => kernelValue α (x-y) • f y) (μ d)) ∧
      (∫ y, k (x-y) • f y ∂μ d) = potentialValue α f x

/-- The absolute-existence part of the endpoint, recorded separately so it can
be checked before the quantitative estimate. -/
def EndpointAbsoluteExistence : Prop :=
  ∀ {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (α : ℝ), 0 < α → α < d → ∀ (f : Point d → 𝕜), Integrable f (μ d) →
    ∀ᵐ x ∂μ d, Integrable (fun y => kernelValue α (x-y) • f y) (μ d)

def StrongBound : Prop :=
  ∀ (d : ℕ) [NeZero d] (α : ℝ), 0 < α → α < d →
    ∀ (p q : ℝ), 1 < p → p < (d : ℝ) / α →
      1 / q = 1 / p - α / (d : ℝ) →
      ∃ C : ℝ≥0, ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
        (f : Point d → 𝕜), MemLp f (ENNReal.ofReal p) (μ d) →
        (∀ᵐ x ∂μ d, Integrable (fun y => kernelValue α (x-y) • f y) (μ d)) ∧
        MemLp (potentialValue α f) (ENNReal.ofReal q) (μ d) ∧
        eLpNorm (potentialValue α f) (ENNReal.ofReal q) (μ d) ≤
          (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (μ d)

def WeakEndpoint : Prop :=
  ∀ (d : ℕ) [NeZero d] (α : ℝ), 0 < α → α < d →
    ∃ C : ℝ≥0, ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
      (f : Point d → 𝕜), Integrable f (μ d) →
      (∀ᵐ x ∂μ d, Integrable (fun y => kernelValue α (x-y) • f y) (μ d)) ∧
      Measurable (potentialValue α f) ∧
      P102.U2.weakSize (μ d) ((d : ℝ) / ((d : ℝ) - α)) (potentialValue α f) ≤
        (C : ℝ≥0∞) * eLpNorm f 1 (μ d)
end P102.U2.RieszPotentialsSpec
