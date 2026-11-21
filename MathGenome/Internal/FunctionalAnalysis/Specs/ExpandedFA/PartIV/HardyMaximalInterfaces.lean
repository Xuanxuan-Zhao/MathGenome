import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.AtomicHardySpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.Analysis.Convolution
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
Interfaces for the fixed-kernel chapter, paper.tex:19990--20110.
The chapter assumes d ≥ 1. The definitions also make sense in dimension zero;
the continuity assertions below hold there as well. Suprema take values in
ℝ≥0∞, so unbounded maximal functions are retained. Coordinate words encode
multi-indices, including the empty word (the function itself).
The existence of the lowpass and inverse is the separate HardyLowpass goal.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Convolution

namespace ExpandedFA.PartIV.HardyMaximalSpec
open ExpandedFA.Fourier

abbrev L1 (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  ExpandedFA.Hardy.AtomicHardySpaceSpec.L1
    (𝕜 := 𝕜) (volume : Measure (Euclidean d))
abbrev Hardy (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  ExpandedFA.Hardy.AtomicHardySpaceSpec.HardyValue
    (𝕜 := 𝕜) (volume : Measure (Euclidean d))

def coordinatePartial {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (a : Fin k → Fin d) (φ : Euclidean d → 𝕜) (x : Euclidean d) : 𝕜 :=
  iteratedFDeriv ℝ k φ x (fun i => basisVector (a i))

/-- Precisely the smooth polynomial-decay assumptions of the fixed theorem.
The integral is the ordinary Bochner integral, with no conjugation. -/
def IsFixedKernel {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (φ : Euclidean d → 𝕜) : Prop :=
  ContDiff ℝ ∞ φ ∧ (∫ x, φ x) ≠ 0 ∧
    ∀ (k : ℕ) (a : Fin k → Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖coordinatePartial a φ x‖ ≤ C / (1 + ‖x‖) ^ (d + 1 + k)

/-- φ_t(x)=t^{-d} φ(x/t); all maximal-function scales below are positive. -/
def dilate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (t : ℝ) (φ : Euclidean d → 𝕜) (x : Euclidean d) : 𝕜 :=
  (t ^ d)⁻¹ • φ (t⁻¹ • x)

/-- Native Mathlib convolution, using scalar multiplication in the scalar field. -/
def convolve {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u f : Euclidean d → 𝕜) : Euclidean d → 𝕜 :=
  u ⋆[ContinuousLinearMap.mul 𝕜 𝕜, volume] f

abbrev Scale := {t : ℝ // 0 < t}

def radial {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ f : Euclidean d → 𝕜) (x : Euclidean d) : ℝ≥0∞ :=
  ⨆ t : Scale, ENNReal.ofReal ‖convolve (dilate t.val φ) f x‖

/-- The actual pointwise weighted supremum, not an essential supremum. -/
def weightedNorm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal ((1 + ‖x‖) ^ ((d : ℝ) + 1 / 2) * ‖u x‖)

def peetreExponent (d : ℕ) : ℕ := d + 1

def averagingExponent (d : ℕ) : ℝ := 1 - 1 / (4 * ((d : ℝ) + 1))

def AdmissibleOrder (d N : ℕ) : Prop := 2 * peetreExponent d + d + 4 < N

/-- Compact smooth tests with support in the unit ball, and each coordinate
partial derivative of order at most N bounded by one. -/
def IsTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (N : ℕ)
    (ψ : Euclidean d → 𝕜) : Prop :=
  ContDiff ℝ ∞ ψ ∧ tsupport ψ ⊆ Metric.ball 0 1 ∧
    ∀ (k : ℕ), k ≤ N → ∀ (a : Fin k → Fin d) (x : Euclidean d),
      ‖coordinatePartial a ψ x‖ ≤ 1

abbrev Tests (𝕜 : Type) [RCLike 𝕜] (d N : ℕ) :=
  {ψ : Euclidean d → 𝕜 // IsTest N ψ}

def grand {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (N : ℕ) (f : Euclidean d → 𝕜) (x : Euclidean d) : ℝ≥0∞ :=
  ⨆ t : Scale, ⨆ ψ : Tests 𝕜 d N,
    ENNReal.ofReal ‖convolve (dilate t.val ψ.val) f x‖

/-- η is the chosen Schwartz lowpass. The cutoff hypotheses are needed for
later estimates, but neither for this definition nor for lower semicontinuity. -/
def peetre {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (f : Euclidean d → 𝕜) (x : Euclidean d) : ℝ≥0∞ :=
  ⨆ j : ℤ, ⨆ y : Euclidean d,
    ENNReal.ofReal (‖convolve (dilate ((2 : ℝ) ^ (-j)) η) f y‖ /
      (1 + (2 : ℝ) ^ j * ‖x - y‖) ^ peetreExponent d)

end ExpandedFA.PartIV.HardyMaximalSpec

namespace ExpandedFA.PartIV.HardyMaximalSpec.Spec
open ExpandedFA.Fourier

def L1Type := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), Type
def L1Value : L1Type := @HardyMaximalSpec.L1

def HardyType := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), Type
def HardyValue : HardyType := @HardyMaximalSpec.Hardy

def coordinatePartialType := ∀ {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}, (Fin k → Fin d) → (Euclidean d → 𝕜) → Euclidean d → 𝕜
def coordinatePartialValue : coordinatePartialType := @HardyMaximalSpec.coordinatePartial

def IsFixedKernelType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, (Euclidean d → 𝕜) → Prop
def IsFixedKernelValue : IsFixedKernelType := @HardyMaximalSpec.IsFixedKernel

def dilateType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, ℝ → (Euclidean d → 𝕜) → Euclidean d → 𝕜
def dilateValue : dilateType := @HardyMaximalSpec.dilate

def convolveType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, (Euclidean d → 𝕜) → (Euclidean d → 𝕜) → Euclidean d → 𝕜
def convolveValue : convolveType := @HardyMaximalSpec.convolve

def radialType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, (Euclidean d → 𝕜) → (Euclidean d → 𝕜) → Euclidean d → ℝ≥0∞
def radialValue : radialType := @HardyMaximalSpec.radial

def weightedNormType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, (Euclidean d → 𝕜) → ℝ≥0∞
def weightedNormValue : weightedNormType := @HardyMaximalSpec.weightedNorm

def peetreExponentType := ℕ → ℕ
def peetreExponentValue : peetreExponentType := @HardyMaximalSpec.peetreExponent

def averagingExponentType := ℕ → ℝ
def averagingExponentValue : averagingExponentType := @HardyMaximalSpec.averagingExponent

def AdmissibleOrderType := ℕ → ℕ → Prop
def AdmissibleOrderValue : AdmissibleOrderType := @HardyMaximalSpec.AdmissibleOrder

def IsTestType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, ℕ → (Euclidean d → 𝕜) → Prop
def IsTestValue : IsTestType := @HardyMaximalSpec.IsTest

def TestsType := ∀ (𝕜 : Type) [RCLike 𝕜] (d N : ℕ), Type
def TestsValue : TestsType := @HardyMaximalSpec.Tests

def grandType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, ℕ → (Euclidean d → 𝕜) → Euclidean d → ℝ≥0∞
def grandValue : grandType := @HardyMaximalSpec.grand

def peetreType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, Schwartz 𝕜 d → (Euclidean d → 𝕜) → Euclidean d → ℝ≥0∞
def peetreValue : peetreType := @HardyMaximalSpec.peetre

def KernelBounded : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  (φ : Euclidean d → 𝕜), IsFixedKernel φ → BddAbove (Set.range fun x => ‖φ x‖)

def TestBounded : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
  (ψ : Tests 𝕜 d N), ∀ x, ‖ψ.val x‖ ≤ 1

def Parameters : Prop := ∀ d : ℕ,
  0 < averagingExponent d ∧ averagingExponent d < 1 ∧
  (d : ℝ) < (peetreExponent d : ℝ) * averagingExponent d ∧
  (peetreExponent d : ℝ) * (1 - averagingExponent d) = 1 / 4 ∧
  ∃ N : ℕ, AdmissibleOrder d N

def ScaledConvolutionContinuous : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  (u f : Euclidean d → 𝕜), Continuous u →
  BddAbove (Set.range fun x => ‖u x‖) → Integrable f → ∀ t : ℝ,
  Continuous (convolve (dilate t u) f)

def RadialRegularity : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  (φ f : Euclidean d → 𝕜), IsFixedKernel φ → Integrable f →
  LowerSemicontinuous (radial φ f) ∧ Measurable (radial φ f)

def GrandRegularity : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  (N : ℕ) (f : Euclidean d → 𝕜), Integrable f →
  LowerSemicontinuous (grand N f) ∧ Measurable (grand N f)

def PeetreRegularity : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  (η : Schwartz 𝕜 d) (f : Euclidean d → 𝕜),
  LowerSemicontinuous (peetre η f) ∧ Measurable (peetre η f)

end ExpandedFA.PartIV.HardyMaximalSpec.Spec
