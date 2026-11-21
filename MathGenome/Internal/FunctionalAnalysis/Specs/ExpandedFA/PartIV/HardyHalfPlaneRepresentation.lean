import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! Independent statements for the representation part of
`paper.tex`, fa2:p4:hardy-halfplane, lines 18894–18928.
The Cayley and inner-factor assertions are allocated to separate goals.
Functions in L²(0,∞) are expressed as measurable representatives with `MemLp`
for restricted Lebesgue measure; uniqueness is almost everywhere. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology FourierTransform

namespace ExpandedFA.PartIV.HardyHalfPlaneRepresentationSpec

abbrev positiveMeasure : Measure ℝ := volume.restrict (Ioi 0)
abbrev BoundaryL2 := Lp ℂ 2 (volume : Measure ℝ)
def upperHalfPlane : Set ℂ := {z | 0 < z.im}
def slice (F : ℂ → ℂ) (y : ℝ) : ℝ → ℂ := fun x => F ((x : ℂ) + (y : ℂ) * Complex.I)
def kernel (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * (t : ℂ))
def laplace (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t, kernel z t * f t ∂positiveMeasure
def damp (f : ℝ → ℂ) (y : ℝ) : ℝ → ℂ :=
  fun t => (Real.exp (-2 * Real.pi * y * t) : ℂ) * f t

/-- Holomorphy and a uniform bound for the actual horizontal square integrals.
`MemLp` ensures these totalized integrals are genuine finite integrals. -/
def IsH2 (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F upperHalfPlane ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y →
      MemLp (slice F y) 2 volume ∧ (∫ x : ℝ, ‖slice F y x‖ ^ 2) ≤ C

/-- Equality is pointwise throughout the open upper half-plane. -/
def Represents (F : ℂ → ℂ) (f : ℝ → ℂ) : Prop :=
  MemLp f 2 positiveMeasure ∧ ∀ z ∈ upperHalfPlane, F z = laplace f z

/-- An actual strong L² limit of horizontal slices, with no given boundary data. -/
def HasBoundary (F : ℂ → ℂ) (b : BoundaryL2) : Prop :=
  ∃ s : ℝ → BoundaryL2,
    (∀ y, 0 < y → (s y : ℝ → ℂ) =ᵐ[volume] slice F y) ∧
    Tendsto s (𝓝[>] (0 : ℝ)) (𝓝 b)

def AbsoluteConvergence : Prop := ∀ (f : ℝ → ℂ), MemLp f 2 positiveMeasure →
  ∀ z ∈ upperHalfPlane, Integrable (fun t => kernel z t * f t) positiveMeasure

def Representation : Prop := ∀ F : ℂ → ℂ, IsH2 F ↔ ∃ f, Represents F f

def RepresentationForward : Prop := ∀ (F : ℂ → ℂ) (f : ℝ → ℂ),
  Represents F f → IsH2 F

def BoundaryOfRepresentation : Prop := ∀ (F : ℂ → ℂ) (f : ℝ → ℂ), Represents F f →
  ∃! b : BoundaryL2, HasBoundary F b

def HorizontalNorm : Prop := ∀ (F : ℂ → ℂ) (f : ℝ → ℂ), Represents F f →
  ∀ y : ℝ, 0 < y → ∃ h : MemLp (slice F y) 2 volume,
    ‖h.toLp (slice F y)‖ = (eLpNorm (damp f y) 2 positiveMeasure).toReal

def BoundaryConvergence : Prop := ∀ F : ℂ → ℂ, IsH2 F →
  ∃! b : BoundaryL2, HasBoundary F b

/-- This additionally fixes the positive-exponential boundary convention. -/
def BoundaryFourier : Prop := ∀ (F : ℂ → ℂ) (f : ℝ → ℂ), Represents F f →
  ∃ b : BoundaryL2, HasBoundary F b ∧
    ((𝓕 b : BoundaryL2) : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator f

def RepresentationUnique : Prop := ∀ (F : ℂ → ℂ) (f g : ℝ → ℂ),
  Represents F f → Represents F g → f =ᵐ[positiveMeasure] g

/-- Auxiliary estimates for the actual damped frequency density. -/
def DampingBound : Prop := ∀ (f : ℝ → ℂ), MemLp f 2 positiveMeasure →
  ∀ y : ℝ, 0 ≤ y → MemLp (damp f y) 2 positiveMeasure ∧
    eLpNorm (damp f y) 2 positiveMeasure ≤ eLpNorm f 2 positiveMeasure

def DampingConvergence : Prop := ∀ (f : ℝ → ℂ), MemLp f 2 positiveMeasure →
  Tendsto (fun y : ℝ => eLpNorm (damp f y - f) 2 positiveMeasure)
    (𝓝[>] 0) (𝓝 0)

end ExpandedFA.PartIV.HardyHalfPlaneRepresentationSpec
