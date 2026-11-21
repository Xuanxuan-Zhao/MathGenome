import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinKernelMinus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support

/-! Independent statements for `fa2:p4:krein-odd` in the adopted source.
Tests are real continuous compactly supported functions, with their usual
Lebesgue quadratic integral. The measure in the compensated formula need not
have finite total mass, and the additive constant has no sign restriction. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.PartIV.KreinOdd.Spec

/-- The actual quadratic integral appearing in the manuscript. -/
def quadraticForm (q f : ℝ → ℝ) : ℝ :=
  ∫ s : ℝ, ∫ t : ℝ, q (s - t) * f s * f t

def OddTestPositive (q : ℝ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → Function.Odd f →
    0 ≤ quadraticForm q f

/-- Positive locally finite Borel measure, absolute convergence, the prescribed
zero-parameter compensation, and one integrable majorant on every compact
spatial interval. -/
def Representation (q : ℝ → ℝ) : Prop :=
  ∃ ν : Measure ℝ, IsLocallyFiniteMeasure ν ∧
    (∀ s : ℝ, Integrable (fun ξ => KreinKernelMinus.Spec.compensated ξ s) ν) ∧
    (∀ s : ℝ, q s = q 0 + ∫ ξ, KreinKernelMinus.Spec.compensated ξ s ∂ν) ∧
    KreinKernelMinus.Spec.CompactDomination ν

def TestKernelEquivalence : Prop :=
  ∀ q : ℝ → ℝ, Continuous q → Function.Even q →
    (OddTestPositive q ↔
      KreinSolutions.Specs.PositiveDefiniteValue (KreinSolutions.Specs.KernelMinusValue q))

def Main : Prop :=
  ∀ q : ℝ → ℝ, Continuous q → Function.Even q →
    (OddTestPositive q ↔ Representation q)

def ConstantFreedom : Prop :=
  ∀ (q : ℝ → ℝ) (c : ℝ), Continuous q → Function.Even q →
    (OddTestPositive (fun s => q s + c) ↔ OddTestPositive q)

/-- Allowing all real frequencies only enlarges the forbidden class: by the
evenness of cosine and cosh this is equivalent to using nonnegative frequencies.
Absolute integrability is automatic for cosine with a finite positive measure;
for cosh it is explicitly required, as in a finite-valued mixture formula. -/
def FiniteMixtureDifference (q : ℝ → ℝ) : Prop :=
  ∃ μ θ : Measure ℝ, IsFiniteMeasure μ ∧ IsFiniteMeasure θ ∧
    (∀ s : ℝ, Integrable (fun b => Real.cosh (b * s)) θ) ∧
    (∀ s : ℝ, q s = (∫ a, Real.cos (a * s) ∂μ) - ∫ b, Real.cosh (b * s) ∂θ)

def QuadraticExample : Prop :=
  Continuous (fun s : ℝ => -(s ^ 2)) ∧ Function.Even (fun s : ℝ => -(s ^ 2)) ∧
    OddTestPositive (fun s : ℝ => -(s ^ 2)) ∧
    (∀ s t : ℝ, KreinSolutions.Specs.KernelMinusValue (fun u => -(u ^ 2)) s t = 2 * s * t) ∧
    Representation (fun s : ℝ => -(s ^ 2))

def QuadraticAtom : Prop :=
  let ν : Measure ℝ := (2 : ℝ≥0∞) • Measure.dirac 0
  IsLocallyFiniteMeasure ν ∧
    (∀ s : ℝ, Integrable (fun ξ => KreinKernelMinus.Spec.compensated ξ s) ν) ∧
    (∀ s : ℝ, -(s ^ 2) = ∫ ξ, KreinKernelMinus.Spec.compensated ξ s ∂ν) ∧
    KreinKernelMinus.Spec.CompactDomination ν

def QuadraticCounterexample : Prop :=
  ¬FiniteMixtureDifference (fun s : ℝ => -(s ^ 2))

end ExpandedFA.PartIV.KreinOdd.Spec
