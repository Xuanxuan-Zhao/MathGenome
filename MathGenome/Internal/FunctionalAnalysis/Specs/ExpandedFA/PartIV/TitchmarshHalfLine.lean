import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardySupportBridge

/-! The two assertions of `fa2:p4:titchmarsh-halfline` (paper.tex
19019–19044). Half-line functions are representatives for restricted Lebesgue
measure, extended by zero before using the shared essential-support interface.
The Laplace transform has the source's positive sign and factor `2π`.
The bounded-transform criterion includes the zero function and `c = 0`. -/
noncomputable section
open MeasureTheory Set

namespace ExpandedFA.PartIV.TitchmarshHalfLine
open HardyHalfPlaneRepresentationSpec HardySupportBridge HardyExponentialFactor

/-- Canonical representative on the whole real line. -/
def extend (f : ℝ → ℂ) : ℝ → ℂ := (Ioi 0).indicator f

/-- The ordinary integral convolution of the zero extensions. -/
def halfConvolution (f g : ℝ → ℂ) : ℝ → ℂ := convolution (extend f) (extend g)

/-- Vanishing means almost everywhere on the open interval, with no prescribed
values at its endpoints. -/
def VanishesInitially (f : ℝ → ℂ) (c : ℝ) : Prop :=
  f =ᵐ[volume.restrict (Ioo 0 c)] 0

def BoundedShift (f : ℝ → ℂ) (c : ℝ) : Prop :=
  ∃ M : ℝ, ∀ z ∈ upperHalfPlane,
    ‖exponentialInner (-(2 * Real.pi * c)) z * laplace f z‖ ≤ M

namespace Spec

/-- Existence of all three finite essential endpoints, nonvanishing of the
convolution, and addition. No square integrability or compact support is assumed. -/
def ConvolutionEndpoints : Prop := ∀ f g : ℝ → ℂ,
  Integrable f positiveMeasure → Integrable g positiveMeasure →
  ¬ (f =ᵐ[positiveMeasure] 0) → ¬ (g =ᵐ[positiveMeasure] 0) →
  Integrable (halfConvolution f g) ∧ ¬ (halfConvolution f g =ᵐ[volume] 0) ∧
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    IsLeftEndpoint (extend f) a ∧ IsLeftEndpoint (extend g) b ∧
    IsLeftEndpoint (halfConvolution f g) (a + b)

/-- The same identity for any given choices of the lower endpoints. -/
def EndpointAddition : Prop := ∀ f g : ℝ → ℂ,
  Integrable f positiveMeasure → Integrable g positiveMeasure →
  ¬ (f =ᵐ[positiveMeasure] 0) → ¬ (g =ᵐ[positiveMeasure] 0) →
  ∀ a b : ℝ, IsLeftEndpoint (extend f) a → IsLeftEndpoint (extend g) b →
  ¬ (halfConvolution f g =ᵐ[volume] 0) ∧
    IsLeftEndpoint (halfConvolution f g) (a + b)

def BoundedTransformCriterion : Prop := ∀ f : ℝ → ℂ,
  Integrable f positiveMeasure → ∀ c : ℝ, 0 ≤ c →
    (VanishesInitially f c ↔ BoundedShift f c)

end Spec
/-- Real-valued representatives use their own ordinary real integral
convolution. The complex theorem is transferred through the scalar inclusion. -/
def realExtend (f : ℝ → ℝ) : ℝ → ℝ := (Ioi 0).indicator f

def realHalfConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, realExtend f t * realExtend g (x - t)

def IsRealLeftEndpoint (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ c : ℝ, (∀ᵐ t ∂(volume : Measure ℝ), t < c → f t = 0) ↔ c ≤ a

namespace Spec

def RealConvolutionEndpoints : Prop := ∀ f g : ℝ → ℝ,
  Integrable f positiveMeasure → Integrable g positiveMeasure →
  ¬ (f =ᵐ[positiveMeasure] 0) → ¬ (g =ᵐ[positiveMeasure] 0) →
  Integrable (realHalfConvolution f g) ∧ ¬ (realHalfConvolution f g =ᵐ[volume] 0) ∧
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    IsRealLeftEndpoint (realExtend f) a ∧ IsRealLeftEndpoint (realExtend g) b ∧
    IsRealLeftEndpoint (realHalfConvolution f g) (a + b)

def RealBoundedTransformCriterion : Prop := ∀ f : ℝ → ℝ,
  Integrable f positiveMeasure → ∀ c : ℝ, 0 ≤ c →
    (f =ᵐ[volume.restrict (Ioo 0 c)] 0 ↔ BoundedShift (fun t => (f t : ℂ)) c)

end Spec

end ExpandedFA.PartIV.TitchmarshHalfLine
