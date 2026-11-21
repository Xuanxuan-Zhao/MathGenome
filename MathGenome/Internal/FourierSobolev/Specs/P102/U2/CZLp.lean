import MathGenome.Internal.FourierSobolev.Specs.P102.U2.CZWeakExtension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator

/-! Independent statements for the complete Theorem p102:U2-03
(paper.tex:953–976). The general theorem uses exactly `KernelHypotheses`;
smoothness occurs only in the separate sufficient condition. All constants are
finite, nonnegative, and uniform over operators and kernels with the given data.
The endpoint extension includes the upstream uniqueness and sum-space action.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace P102.U2.CZLpData
open CZWeak

/-- All and only the finite exponents strictly greater than one. -/
structure Exponent where
  val : ℝ≥0∞
  one_lt : 1 < val
  lt_top : val < ∞

instance (p : Exponent) : Fact (1 ≤ p.val) := ⟨p.one_lt.le⟩

abbrev Space (d : ℕ) (p : ℝ≥0∞) := Lp ℂ p (volume : Measure (Point d))
abbrev StrongOperator (d : ℕ) (p : Exponent) := Space d p.val →L[ℂ] Space d p.val

/-- Agreement on the entire L²/Lᵖ intersection. -/
def Agrees {d : ℕ} (T : Operator d) (p : Exponent) (R : StrongOperator d p) : Prop :=
  ∀ (f : Point d → ℂ) (hp : MemLp f p.val volume) (h2 : MemLp f 2 volume),
    (R (hp.toLp f) : Point d → ℂ) =ᵐ[volume] (T (h2.toLp f) : Point d → ℂ)

/-- Every pairwise intersection, including inputs outside L², is covered. -/
def PairwiseCompatible {d : ℕ} (R : ∀ p : Exponent, StrongOperator d p) : Prop :=
  ∀ (p q : Exponent) (f : Point d → ℂ)
    (hp : MemLp f p.val volume) (hq : MemLp f q.val volume),
    (R p (hp.toLp f) : Point d → ℂ) =ᵐ[volume] (R q (hq.toLp f) : Point d → ℂ)

def EndpointCompatible {d : ℕ} (S : Extension d)
    (R : ∀ p : Exponent, StrongOperator d p) : Prop :=
  ∀ (p : Exponent) (f : Point d → ℂ)
    (h1 : MemLp f 1 volume) (hp : MemLp f p.val volume),
    (R p (hp.toLp f) : Point d → ℂ) =ᵐ[volume] (S (h1.toLp f) : Point d → ℂ)

/-- The Euclidean length of the complex coordinate gradient. -/
abbrev gradientNorm {d : ℕ} (K : Point d → ℂ) (z : Point d) : ℝ :=
  ExpandedFA.SingularIntegrals.StandardConvolution.kernelGradientNorm K z

/-- Only the integral difference condition, isolated for the sufficient condition. -/
def DifferenceBound {d : ℕ} (K : Point d → ℂ) (A : ℝ≥0) : Prop :=
  ∀ h : Point d, h ≠ 0 →
    (∫⁻ z in {z : Point d | 2 * ‖h‖ < ‖z‖}, ‖K (z - h) - K z‖ₑ) ≤ (A : ℝ≥0∞)

end P102.U2.CZLpData

namespace Specs.P102.U2.CZLp
open _root_.P102.U2.CZWeak _root_.P102.U2.CZLpData

/-- The original complete extension assertion, with no conditional premises. -/
def full_extension : Prop :=
  ∃ (C₁ : ℕ → ℝ≥0 → ℝ≥0 → ℝ≥0)
    (C : ℕ → Exponent → ℝ≥0 → ℝ≥0 → ℝ≥0),
    ∀ (d : ℕ), 0 < d → ∀ (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0),
      KernelHypotheses T K A →
      CoreBound T (C₁ d A ‖T‖₊) ∧
      ∃ (S : Extension d) (R : ∀ p : Exponent, StrongOperator d p),
        Compatible T S ∧ WeakBound S (C₁ d A ‖T‖₊) ∧
        MeasureContinuous S ∧ Approximates T S ∧ UniqueWeakExtension T S ∧ CompatibleSum T S ∧
        (∀ p, ‖R p‖ ≤ C d p A ‖T‖₊) ∧
        (∀ p, Agrees T p (R p)) ∧ PairwiseCompatible R ∧ EndpointCompatible S R

/-- The source's sufficient condition; no pointwise kernel-size hypothesis. -/
def smooth_difference : Prop :=
  ∃ C : ℕ → ℝ≥0, ∀ (d : ℕ), 0 < d →
    ∀ (K : Point d → ℂ) (B : ℝ≥0),
      ContDiffOn ℝ 1 K ({0}ᶜ : Set (Point d)) →
      (∀ z ≠ 0, gradientNorm K z ≤ (B : ℝ) / ‖z‖ ^ (d + 1)) →
      DifferenceBound K (C d * B)

end Specs.P102.U2.CZLp
