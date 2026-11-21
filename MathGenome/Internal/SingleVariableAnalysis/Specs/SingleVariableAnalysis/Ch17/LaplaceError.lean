import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Quantitative part of K03.17.laplace_local, paper.tex:4582–4600.
All derivatives are real. C² is relative to the closed interval; C³ and
Lipschitz regularity are required only on some open neighborhood of x₀.
The integral is the existing proper Darboux integral, with integrability
asserted in the conclusion. In particular no nonzero-amplitude assumption
is made. The separate C²/continuous limit theorem is not strengthened here. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.LaplaceError
open Set Filter Asymptotics MeasureTheory
open scoped Topology
open _root_.SingleVariableAnalysis

/-- The full source quantitative conclusion for each canonical scalar field. -/
def normalizedError : Prop :=
  ∀ k : ScalarKind, letI := LaplaceLocalization.scalarRCLike k
    ∀ (φ : ℝ → ℝ) (g : ℝ → Ch01.Scalar.scalarValue k) (a b x₀ : ℝ),
      ContDiffOn ℝ 2 φ (Icc a b) → ContinuousOn g (Icc a b) →
      x₀ ∈ Ioo a b →
      (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) →
      0 < deriv (deriv φ) x₀ →
      (∃ U : Set ℝ, IsOpen U ∧ x₀ ∈ U ∧ ContDiffOn ℝ 3 φ U) →
      (∃ (U : Set ℝ) (L : NNReal), IsOpen U ∧ x₀ ∈ U ∧ LipschitzOnWith L g U) →
      ∃ hI : ∀ t : ℝ, Ch08.Integral.scalarIntegrableValue k
          (fun x => Real.exp (-t * φ x) • g x) a b,
        IsBigO atTop
          (fun t : ℝ => (Real.sqrt t * Real.exp (t * φ x₀)) •
            Ch08.Integral.scalarIntegralValue k _ (hI t) -
            Real.sqrt (2 * Real.pi / deriv (deriv φ) x₀) • g x₀)
          (fun t : ℝ => (Real.sqrt t)⁻¹)

/-- The cubic Taylor error follows from local C³, without an assumed bound
or a new differentiability hypothesis on the exterior. -/
def cubicRemainder : Prop :=
  ∀ (φ : ℝ → ℝ) (a b x₀ : ℝ),
    ContDiffOn ℝ 2 φ (Icc a b) → x₀ ∈ Ioo a b →
    (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) →
    (∃ U : Set ℝ, IsOpen U ∧ x₀ ∈ U ∧ ContDiffOn ℝ 3 φ U) →
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ a < x₀-r ∧ x₀+r < b ∧
      ∀ h : ℝ, |h| ≤ r →
        |φ (x₀+h) - φ x₀ - deriv (deriv φ) x₀ * h^2 / 2| ≤ C * |h|^3

/-- Finite whole-line moments needed by the local error estimate. -/
def gaussianMomentIntegrable : Prop :=
  ∀ c : ℝ, 0 < c →
    Integrable (fun y : ℝ => (|y| + |y|^3) * Real.exp (-c*y^2))

/-- An explicit exponential bound for the omitted scaled Gaussian tails. -/
def omittedGaussianTail : Prop :=
  ∀ c r : ℝ, 0 < c → 0 < r → ∃ A : ℝ, 0 ≤ A ∧
    ∀ t : ℝ, 0 ≤ t →
      (∫ y in {y : ℝ | r * Real.sqrt t ≤ |y|}, Real.exp (-c*y^2)) ≤
        A * Real.exp (-(c*r^2/2)*t)

/-- Local rescaling error controlled by an explicitly integrable Gaussian
moment. The hypotheses are those of the quantitative source corollary. -/
def localControl : Prop :=
  ∀ k : ScalarKind, letI := LaplaceLocalization.scalarRCLike k
    ∀ (φ : ℝ → ℝ) (g : ℝ → Ch01.Scalar.scalarValue k) (a b x₀ : ℝ),
      ContDiffOn ℝ 2 φ (Icc a b) → ContinuousOn g (Icc a b) →
      x₀ ∈ Ioo a b →
      (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) →
      0 < deriv (deriv φ) x₀ →
      (∃ U : Set ℝ, IsOpen U ∧ x₀ ∈ U ∧ ContDiffOn ℝ 3 φ U) →
      (∃ (U : Set ℝ) (L : NNReal), IsOpen U ∧ x₀ ∈ U ∧ LipschitzOnWith L g U) →
      ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ a < x₀-r ∧ x₀+r < b ∧
        Integrable (fun y : ℝ => (|y|+|y|^3) *
          Real.exp (-(deriv (deriv φ) x₀/4)*y^2)) ∧
        ∀ t : ℝ, 0 < t → ∀ y : ℝ, |y| ≤ r * Real.sqrt t →
          ‖Real.exp (-t*(φ (x₀+y/Real.sqrt t)-φ x₀)) • g (x₀+y/Real.sqrt t) -
            Real.exp (-deriv (deriv φ) x₀*y^2/2) • g x₀‖ ≤
          (Real.sqrt t)⁻¹ * A * (|y|+|y|^3) *
            Real.exp (-(deriv (deriv φ) x₀/4)*y^2)

end Specs.SingleVariableAnalysis.Ch17.LaplaceError
