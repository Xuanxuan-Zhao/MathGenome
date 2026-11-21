import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PositiveHarmonic

/-! Independent statements for the holomorphic part of `fa2:p4:herglotz`,
paper.tex:18577–18612. Positivity means nonnegativity; the zero measure is
included. Functions are constrained only on the open unit disk. -/

noncomputable section

namespace ExpandedFA.PartIV.Herglotz

open Set MeasureTheory
open PositiveHarmonic

/-- The displayed Herglotz integral, with a real imaginary constant. -/
def herglotzTransform (μ : Measure Circle) (c : ℝ) (z : ℂ) : ℂ :=
  Complex.I * (c : ℂ) + ∫ ζ : Circle, ((ζ : ℂ) + z) / ((ζ : ℂ) - z) ∂μ

/-- Holomorphic functions with nonnegative real part on the open disk. -/
def NonnegativeHolomorphic (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F unitDisk ∧ ∀ z ∈ unitDisk, 0 ≤ (F z).re

/-- Representation by a finite positive Radon circle measure and a real constant.
`Measure Circle` is a positive Borel measure, not a signed or complex measure. -/
def Represents (F : ℂ → ℂ) (μ : Measure Circle) (c : ℝ) : Prop :=
  IsFiniteMeasure μ ∧ μ.Regular ∧ ∀ z ∈ unitDisk, F z = herglotzTransform μ c z

namespace Spec

/-- Existence and joint uniqueness of the measure and the imaginary constant. -/
def Representation : Prop :=
  ∀ F : ℂ → ℂ, NonnegativeHolomorphic F →
    ∃! p : Measure Circle × ℝ, Represents F p.1 p.2

/-- The center identifies both parameters for every representation. -/
def CenterNormalization : Prop :=
  ∀ (F : ℂ → ℂ) (μ : Measure Circle) (c : ℝ), Represents F μ c →
    c = (F 0).im ∧ μ.real univ = (F 0).re

/-- Every finite positive circle measure and every real constant give a
holomorphic function with nonnegative real part, with the exact center values. -/
def Converse : Prop :=
  ∀ (μ : Measure Circle) (c : ℝ), IsFiniteMeasure μ →
    NonnegativeHolomorphic (herglotzTransform μ c) ∧
      (herglotzTransform μ c 0).im = c ∧
      (herglotzTransform μ c 0).re = μ.real univ

end Spec
end ExpandedFA.PartIV.Herglotz
