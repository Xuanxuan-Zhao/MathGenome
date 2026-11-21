import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.AtomicHardySpace
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Independent specification for the smooth maximal part of
`fa2:p4:hardy-maximal-forward`, paper.tex:18475--18498.
The Hilbert truncations have their own allocated goal. The supremum is extended
nonnegative, so infinite maximal values are never discarded by `toReal`.
The source's H¹ is the accepted atomic quotient with its quotient norm.
Both scalar fields, every dimension (including zero), and every positive scale
are included. No normalization or nonzero-integral condition is imposed on Φ. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
universe v

namespace ExpandedFA.Hardy.HardySmoothMaximalBoundSpec

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev L1 (d : ℕ) (𝕜 : Type v) [RCLike 𝕜] :=
  AtomicHardySpaceSpec.L1 (𝕜 := 𝕜) (volume : Measure (Space d))
abbrev Atom (d : ℕ) (𝕜 : Type v) [RCLike 𝕜] :=
  AtomicHardySpaceSpec.AtomValue (𝕜 := 𝕜) (volume : Measure (Space d))
abbrev Hardy (d : ℕ) (𝕜 : Type v) [RCLike 𝕜] :=
  AtomicHardySpaceSpec.HardyValue (𝕜 := 𝕜) (volume : Measure (Space d))

/-- Φ_t(x) = t^{-d} Φ(x/t). Only positive t enter the maximal operator. -/
def DilateValue {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (Φ : Space d → 𝕜) (t : ℝ) (x : Space d) : 𝕜 :=
  (t ^ d)⁻¹ • Φ (t⁻¹ • x)

/-- The ordinary Lebesgue convolution, written with the L¹ input in the
integration variable. This equals the symmetric convolution convention. -/
def ConvolutionValue {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (Φ f : Space d → 𝕜) (t : ℝ) (x : Space d) : 𝕜 :=
  ∫ y, DilateValue Φ t (x - y) * f y

def MaximalValue {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (Φ f : Space d → 𝕜) (x : Space d) : ℝ≥0∞ :=
  ⨆ t : ℝ, ⨆ (_ : 0 < t), ‖ConvolutionValue Φ f t x‖ₑ

def DilateType := ∀ {d : ℕ} {𝕜 : Type v} [RCLike 𝕜],
  (Space d → 𝕜) → ℝ → Space d → 𝕜

def ConvolutionType := ∀ {d : ℕ} {𝕜 : Type v} [RCLike 𝕜],
  (Space d → 𝕜) → (Space d → 𝕜) → ℝ → Space d → 𝕜

def MaximalType := ∀ {d : ℕ} {𝕜 : Type v} [RCLike 𝕜],
  (Space d → 𝕜) → (Space d → 𝕜) → Space d → ℝ≥0∞

/-- Agreement with the native convolution, whose unswapped definition has the
bump in the integration variable. -/
def ConvolutionFormula : Prop :=
  ∀ (d : ℕ) {𝕜 : Type v} [RCLike 𝕜] (Φ f : Space d → 𝕜) (t : ℝ) (x : Space d),
    ConvolutionValue Φ f t x =
      MeasureTheory.convolution (DilateValue Φ t) f (ContinuousLinearMap.mul 𝕜 𝕜) volume x

/-- The actual maximal function is independent of the chosen L¹ representative,
pointwise at every output point, with all positive scales retained. -/
def RepresentativeIndependence : Prop :=
  ∀ (d : ℕ) {𝕜 : Type v} [RCLike 𝕜] (Φ f g : Space d → 𝕜),
    f =ᵐ[volume] g → MaximalValue Φ f = MaximalValue Φ g

/-- Pointwise regularity hypotheses used for the atom estimate. This is a
class of actual bounded Lipschitz bumps, not an assumed analytic certificate.
The class includes the C¹ bumps of the manuscript by the mean-value theorem. -/
def KernelControl {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (Φ : Space d → 𝕜) (R : ℝ) (A : ℝ≥0) : Prop :=
  (∀ x, R < ‖x‖ → Φ x = 0) ∧ (∀ x, ‖Φ x‖ ≤ A) ∧ LipschitzWith A Φ

/-- Main assertion for a single arbitrary compactly supported C¹ bump. -/
def SmoothBound : Prop :=
  ∀ (d : ℕ) {𝕜 : Type v} [RCLike 𝕜] (Φ : Space d → 𝕜),
    ContDiff ℝ 1 Φ → HasCompactSupport Φ → ∃ C : ℝ≥0,
    ∀ h : Hardy d 𝕜,
      Measurable (MaximalValue Φ (AtomicHardySpaceSpec.EmbeddingValue volume h)) ∧
      (∫⁻ x, MaximalValue Φ (AtomicHardySpaceSpec.EmbeddingValue volume h) x) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖h‖

/-- Uniformity in the usual bounded C¹ family: each of the function and
first derivative suprema is bounded by A; the support lies in the unit ball.
Using the closed ball includes, in particular, support in the open unit ball. -/
def UniformSmoothBound : Prop :=
  ∀ (d : ℕ) (A : ℝ≥0), ∃ C : ℝ≥0,
    ∀ {𝕜 : Type v} [RCLike 𝕜] (Φ : Space d → 𝕜),
      ContDiff ℝ 1 Φ → Function.support Φ ⊆ Metric.closedBall 0 1 →
      (∀ x, ‖Φ x‖ ≤ A) → (∀ x, ‖fderiv ℝ Φ x‖ ≤ A) →
      ∀ h : Hardy d 𝕜,
        Measurable (MaximalValue Φ (AtomicHardySpaceSpec.EmbeddingValue volume h)) ∧
        (∫⁻ x, MaximalValue Φ (AtomicHardySpaceSpec.EmbeddingValue volume h) x) ≤
          (C : ℝ≥0∞) * ENNReal.ofReal ‖h‖

/-- Analytic atom estimate, with constants independent of the ball of the atom
and the scalar field. General R makes the arbitrary-compact-support case direct. -/
def UniformAtomBound : Prop :=
  ∀ (d : ℕ) (R : ℝ), 0 < R → ∀ A : ℝ≥0, ∃ C : ℝ≥0,
    ∀ {𝕜 : Type v} [RCLike 𝕜] (Φ : Space d → 𝕜), KernelControl Φ R A →
      ∀ a : Atom d 𝕜, (∫⁻ x, MaximalValue Φ a.val x) ≤ C

/-- Nonlinear extension to the genuine completed quotient. The sole analytic
premise is the atom estimate for this actual convolution maximal operator. -/
def AtomicExtension : Prop :=
  ∀ (d : ℕ) {𝕜 : Type v} [RCLike 𝕜] (Φ : Space d → 𝕜),
    Continuous Φ → (∃ B : ℝ≥0, ∀ x, ‖Φ x‖ ≤ B) → ∀ C : ℝ≥0,
    (∀ a : Atom d 𝕜, (∫⁻ x, MaximalValue Φ a.val x) ≤ C) →
    ∀ h : Hardy d 𝕜,
      Measurable (MaximalValue Φ (AtomicHardySpaceSpec.EmbeddingValue volume h)) ∧
      (∫⁻ x, MaximalValue Φ (AtomicHardySpaceSpec.EmbeddingValue volume h) x) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖h‖

end ExpandedFA.Hardy.HardySmoothMaximalBoundSpec
