import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinKernelPlus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support

/-! Independent statements for the representation part of `fa2:p4:krein-even`.
The separately allocated extreme-point theorem is not asserted here. -/
noncomputable section
open MeasureTheory Set

namespace ExpandedFA.PartIV.KreinEven.Spec
open KreinSolutions.Specs

/-- The original real, even, continuous, compactly supported test condition. -/
def EvenTestPositive (p : ℝ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → Function.Even f → HasCompactSupport f →
    0 ≤ ∫ s, ∫ t, p (s - t) * f s * f t

/-- The finite positive spectral measure and every positive-side cosh moment.
Measures on ℝ carry its Borel sigma algebra. -/
def Represents (p : ℝ → ℝ) (ν : Measure ℝ) : Prop :=
  IsFiniteMeasure ν ∧ ν.real univ = p 0 ∧
    (∀ s : ℝ, Integrable (fun ξ => CValue ξ s) ν ∧ p s = ∫ ξ, CValue ξ s ∂ν) ∧
    ∀ R : ℝ, 0 < R →
      IntegrableOn (fun ξ => Real.cosh (R * Real.sqrt ξ)) (Ioi 0) ν

/-- An actual pair of frequency measures: cosine frequencies are nonnegative;
cosh frequencies are strictly positive. Thus the constant atom occurs only in
one part. The mass of either part is allowed to be zero. -/
def Mixture (p : ℝ → ℝ) (α β : Measure ℝ) : Prop :=
  IsFiniteMeasure α ∧ IsFiniteMeasure β ∧ α (Iio 0) = 0 ∧ β (Iic 0) = 0 ∧
    α.real univ + β.real univ = p 0 ∧
    (∀ s : ℝ,
      Integrable (fun a => Real.cos (a * s)) α ∧
      Integrable (fun b => Real.cosh (b * s)) β ∧
      p s = (∫ a, Real.cos (a * s) ∂α) + ∫ b, Real.cosh (b * s) ∂β) ∧
    ∀ R : ℝ, 0 < R → Integrable (fun b => Real.cosh (R * b)) β

/-- A single integrable bound on each compact time interval. -/
def CompactDomination : Prop :=
  ∀ (p : ℝ → ℝ) (ν : Measure ℝ), Represents p ν → ∀ R : ℝ, 0 < R →
    ∃ g : ℝ → ℝ, Integrable g ν ∧
      ∀ ξ s : ℝ, |s| ≤ R → |CValue ξ s| ≤ g ξ

def IntegralKernelEquivalence : Prop :=
  ∀ p : ℝ → ℝ, Continuous p → Function.Even p →
    (EvenTestPositive p ↔ PositiveDefiniteValue (KernelPlusValue p))

def KernelRepresentation : Prop :=
  ∀ p : ℝ → ℝ, Continuous p → Function.Even p →
    (PositiveDefiniteValue (KernelPlusValue p) ↔ ∃ ν : Measure ℝ, Represents p ν)

def Representation : Prop :=
  ∀ p : ℝ → ℝ, Continuous p → Function.Even p →
    (EvenTestPositive p ↔ ∃ ν : Measure ℝ, Represents p ν)

def MixtureEquivalence : Prop :=
  ∀ p : ℝ → ℝ,
    (∃ ν : Measure ℝ, Represents p ν) ↔ ∃ α β : Measure ℝ, Mixture p α β

end ExpandedFA.PartIV.KreinEven.Spec
