import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-! Independent statements for the positive harmonic part of `fa2:p4:herglotz`,
paper.tex:18577–18612. The holomorphic representation is allocated separately.
All functions are considered only on the open disk; their values outside it
are unrestricted. Measures are positive Borel measures, with finiteness and
Radon regularity required explicitly. -/

noncomputable section

namespace ExpandedFA.PartIV.PositiveHarmonic

open Set MeasureTheory InnerProductSpace

/-- The open unit disk in the complex plane. -/
def unitDisk : Set ℂ := {z | ‖z‖ < 1}

/-- Normalized circle Haar measure. The top positive compact is the whole circle. -/
def circleHaar : Measure Circle := Measure.haarMeasure ⊤

/-- The Poisson kernel for normalized Haar measure, with no `1 / (2 * π)` factor. -/
def circlePoissonKernel (z : ℂ) (ζ : Circle) : ℝ :=
  (1 - ‖z‖ ^ 2) / ‖(ζ : ℂ) - z‖ ^ 2

/-- The finite-measure Poisson extension, defined on the ambient plane. -/
def poissonExtension (μ : Measure Circle) (z : ℂ) : ℝ :=
  ∫ ζ, circlePoissonKernel z ζ ∂μ

/-- Nonnegative harmonicity, including the identically zero function. -/
def NonnegativeHarmonic (u : ℂ → ℝ) : Prop :=
  HarmonicOnNhd u unitDisk ∧ ∀ z ∈ unitDisk, 0 ≤ u z

/-- The full representation predicate, including mass at the center. -/
def Represents (u : ℂ → ℝ) (μ : Measure Circle) : Prop :=
  IsFiniteMeasure μ ∧ μ.Regular ∧
    (∀ z ∈ unitDisk, u z = poissonExtension μ z) ∧ μ.real univ = u 0

namespace Spec

/-- Every nonnegative harmonic function on the open disk has exactly one
finite positive Radon representing measure. -/
def Representation : Prop :=
  ∀ u : ℂ → ℝ, NonnegativeHarmonic u → ∃! μ : Measure Circle, Represents u μ

/-- Every finite positive circle Radon measure gives a nonnegative harmonic
Poisson extension with the stated total mass. -/
def Converse : Prop :=
  ∀ μ : Measure Circle, IsFiniteMeasure μ → μ.Regular →
    NonnegativeHarmonic (poissonExtension μ) ∧
    poissonExtension μ 0 = μ.real univ

/-- Normalization relative to the probability Haar measure used in the source. -/
def HaarNormalization : Prop :=
  IsProbabilityMeasure circleHaar ∧ circleHaar.Regular ∧
    ∀ z ∈ unitDisk, poissonExtension circleHaar z = 1

/-- The zero boundary measure covers the zero-function case. -/
def ZeroExtension : Prop := poissonExtension 0 = 0

end Spec
end ExpandedFA.PartIV.PositiveHarmonic
