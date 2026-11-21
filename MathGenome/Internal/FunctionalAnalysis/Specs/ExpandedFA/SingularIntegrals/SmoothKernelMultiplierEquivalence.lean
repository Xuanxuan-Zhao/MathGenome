import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.TemperedExamples
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Independent statements for paper.tex, `fa2:p4:cz-multiplier` (18294–18339).
The LF distribution is not assumed tempered. Its off-zero function is on the
Euclidean realization of ℝᵈ used by the accepted Fourier convention.
Bumps have amplitude one, rather than integral one: their dilations are
φ(x/r), with no factor r⁻ᵈ. The Cᴺ norm is the maximum of the Fréchet derivative
operator norms through order N. This is a standard Cᴺ norm; in fixed dimension
it is equivalent to the maximum of the coordinate partial derivative norms.
All tests remain smooth; N bounds only the finitely many derivatives in the
normalization. This is the distributional meaning of the source's Cᴺ bumps. -/

open MeasureTheory Set TopologicalSpace
open scoped SchwartzMap ContDiff

noncomputable section
namespace ExpandedFA.SingularIntegrals
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples

abbrev KernelDistribution (d : ℕ) := ScalarDistribution ℂ (⊤ : Opens (Domain d))

/-- Precomposition by x ↦ x/r, without amplitude normalization. -/
def dilateTest {d : ℕ} (r : ℝ) (hr : r ≠ 0)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) : Tests ℂ (⊤ : Opens (Domain d)) :=
  ⟨fun x => φ (r⁻¹ • x), φ.contDiff.comp (contDiff_id.const_smul r⁻¹),
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)),
    subset_univ _⟩

/-- A unit-ball bump with uniformly bounded derivatives through order N. -/
def NormalizedBump {d : ℕ} (N : ℕ) (φ : Tests ℂ (⊤ : Opens (Domain d))) : Prop :=
  tsupport (testSchwartz ℂ φ) ⊆ Metric.closedBall 0 1 ∧
    ∀ n ≤ N, ∀ x : Euclidean d, ‖iteratedFDeriv ℝ n (testSchwartz ℂ φ) x‖ ≤ 1

/-- The same constant works for every bump and every positive scale. -/
def BumpCancellation {d : ℕ} (K : KernelDistribution d) (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ φ, NormalizedBump N φ → ∀ r : ℝ, ∀ hr : 0 < r,
    ‖K (dilateTest r hr.ne' φ)‖ ≤ C

/-- Agreement is distributional off zero, and includes ordinary integrability
on each test supported there. The value of k at zero is irrelevant. -/
def AgreesOffZero {d : ℕ} (K : KernelDistribution d) (k : Euclidean d → ℂ) : Prop :=
  ∀ φ : Tests ℂ (⊤ : Opens (Domain d)), 0 ∉ tsupport (testSchwartz ℂ φ) →
    Integrable (fun x => k x * testSchwartz ℂ φ x) ∧
      K φ = ∫ x, k x * testSchwartz ℂ φ x

/-- All coordinate mixed derivatives, including order zero. Coordinate words
have harmless repetitions and enumerate all multi-indices. -/
def KernelBounds {d : ℕ} (K : KernelDistribution d) (k : Euclidean d → ℂ) : Prop :=
  AgreesOffZero K k ∧ ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)) ∧
    ∀ (n : ℕ) (w : Fin n → Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d, x ≠ 0 →
      ‖iteratedFDeriv ℝ n k x (fun j => basisVector (w j))‖ ≤ C * (‖x‖ ^ (d + n))⁻¹

/-- Equality on every original LF test, not just tests supported off zero. -/
def ExtendsKernel {d : ℕ} (U : Tempered ℂ d) (K : KernelDistribution d) : Prop :=
  ∀ φ, U (testSchwartz ℂ φ) = K φ

def HasTemperedExtension {d : ℕ} (K : KernelDistribution d) : Prop :=
  ∃ U : Tempered ℂ d, ExtendsKernel U K

/-- Global equality of tempered distributions: a point-supported term at
frequency zero cannot be discarded. -/
def FourierRepresentedBy {d : ℕ} (U : Tempered ℂ d) (m : Euclidean d → ℂ) : Prop :=
  ∀ φ : Schwartz ℂ d, Integrable (fun x => m x * φ x) ∧
    temperedFourier U φ = ∫ x, m x * φ x

/-- Off-zero frequency agreement only. This intentionally does not assert the
main global equality: a point-supported discrepancy may remain. -/
def FourierAgreesOffZero {d : ℕ} (U : Tempered ℂ d) (m : Euclidean d → ℂ) : Prop :=
  ∀ φ : Tests ℂ (⊤ : Opens (Domain d)), 0 ∉ tsupport (testSchwartz ℂ φ) →
    Integrable (fun x => m x * testSchwartz ℂ φ x) ∧
      temperedFourier U (testSchwartz ℂ φ) = ∫ x, m x * testSchwartz ℂ φ x

/-- A representative of an L∞ function may always be chosen pointwise bounded.
Measurability and the ordinary Lebesgue integral are explicit. -/
def BoundedFunction {d : ℕ} (m : Euclidean d → ℂ) : Prop :=
  AEStronglyMeasurable m volume ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖m x‖ ≤ M

def SymbolBounds {d : ℕ} (m : Euclidean d → ℂ) : Prop :=
  ContDiffOn ℝ ∞ m ({0}ᶜ : Set (Euclidean d)) ∧
    ∀ (n : ℕ) (w : Fin n → Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d, x ≠ 0 →
      ‖iteratedFDeriv ℝ n m x (fun j => basisVector (w j))‖ ≤ C * (‖x‖ ^ n)⁻¹

def HasBoundedFourier {d : ℕ} (K : KernelDistribution d) : Prop :=
  ∃ (U : Tempered ℂ d) (m : Euclidean d → ℂ),
    ExtendsKernel U K ∧ BoundedFunction m ∧ FourierRepresentedBy U m

def HasSmoothMultiplier {d : ℕ} (K : KernelDistribution d) : Prop :=
  ∃ (U : Tempered ℂ d) (m : Euclidean d → ℂ),
    ExtendsKernel U K ∧ BoundedFunction m ∧ FourierRepresentedBy U m ∧ SymbolBounds m

end ExpandedFA.SingularIntegrals

namespace Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence
open _root_.ExpandedFA.SingularIntegrals _root_.ExpandedFA.Fourier
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Fourier.Examples

/-- Temperedness follows from the kernel bounds without any cancellation. -/
def temperednessType : Prop := ∀ (d : ℕ) (K : KernelDistribution d) (k : Euclidean d → ℂ),
  KernelBounds K k → HasTemperedExtension K

/-- The forward implication includes global representation at frequency zero. -/
def bumpToSymbolType : Prop := ∀ (d : ℕ) (K : KernelDistribution d) (k : Euclidean d → ℂ),
  KernelBounds K k → (∃ N : ℕ, d < N ∧ BumpCancellation K N) → HasSmoothMultiplier K

/-- This direction needs no physical kernel assumptions. -/
def boundedToBumpsType : Prop := ∀ (d : ℕ) (K : KernelDistribution d),
  HasBoundedFourier K → ∃ N : ℕ, d < N ∧ BumpCancellation K N

/-- The order and constant depend only on the dimension, and not on the bump. -/
def bumpFourierL1Type : Prop := ∀ d : ℕ, ∃ N : ℕ, d < N ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
    NormalizedBump N φ → ∫ x, ‖schwartzFourier (testSchwartz ℂ φ) x‖ ≤ C

/-- Full original obligation, with an existential sufficiently large fixed N. -/
def equivalenceType : Prop := ∀ (d : ℕ) (K : KernelDistribution d) (k : Euclidean d → ℂ),
  KernelBounds K k → HasTemperedExtension K ∧
    ((∃ N : ℕ, d < N ∧ BumpCancellation K N) ↔ HasSmoothMultiplier K) ∧
    (HasBoundedFourier K ↔ HasSmoothMultiplier K)

/-- Quantitative duality estimate used in the bounded-multiplier implication. -/
def boundedFourierPairingType : Prop := ∀ (d : ℕ) (U : Tempered ℂ d)
    (m : Euclidean d → ℂ) (M : ℝ),
  0 ≤ M → (∀ x, ‖m x‖ ≤ M) → FourierRepresentedBy U m →
    ∀ φ : Schwartz ℂ d, ‖U φ‖ ≤ M * ∫ x, ‖schwartzFourier φ x‖

/-- Compact unit support converts any fixed Schwartz seminorm into a Cᴺ bound. -/
def bumpSeminormType : Prop := ∀ (d N k n : ℕ) (φ : Tests ℂ (⊤ : Opens (Domain d))),
  NormalizedBump N φ → n ≤ N → SchwartzMap.seminorm ℂ k n (testSchwartz ℂ φ) ≤ 1

/-- The zero-dimensional Fourier space is a singleton of volume one. Every
LF distribution there has a constant smooth multiplier, with no kernel or
cancellation assumptions. -/
def zeroDimensionType : Prop := ∀ K : KernelDistribution 0, HasSmoothMultiplier K

/-- The cancellation constant also controls arbitrary unit-support tests by
any positive common bound for their first N derivatives. -/
def bumpPairingBoundType : Prop := ∀ (d N : ℕ) (K : KernelDistribution d),
  BumpCancellation K N → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (φ : Tests ℂ (⊤ : Opens (Domain d))) (B : ℝ), 0 < B →
      tsupport (testSchwartz ℂ φ) ⊆ Metric.closedBall 0 1 →
      (∀ n ≤ N, ∀ x : Euclidean d,
        ‖iteratedFDeriv ℝ n (testSchwartz ℂ φ) x‖ ≤ B) →
      ∀ (r : ℝ) (hr : 0 < r), ‖K (dilateTest r hr.ne' φ)‖ ≤ C * B

/-- Original compact test functions determine every tempered pairing. -/
def temperedExtType : Prop := ∀ (d : ℕ) (U V : Tempered ℂ d),
  (∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
    U (testSchwartz ℂ φ) = V (testSchwartz ℂ φ)) → U = V

/-- The source's annular integration-by-parts estimate, including all
frequency derivatives and a constant uniform in the physical radius. -/
def annularFourierDecayType : Prop := ∀ (d : ℕ) (K : KernelDistribution d)
    (k : Euclidean d → ℂ), KernelBounds K k →
  ∀ (a : Euclidean d → ℂ), ContDiff ℝ ∞ a → HasCompactSupport a →
    tsupport a ⊆ Metric.closedBall 0 1 →
  ∀ (ρ : ℝ), 0 < ρ → (∀ x ∈ tsupport a, ρ ≤ ‖x‖) →
  ∀ (n L : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r →
    ∃ φ : Tests ℂ (⊤ : Opens (Domain d)),
      ⇑(testSchwartz ℂ φ) = (fun x => a (r⁻¹ • x) * k x) ∧
      ∀ ξ : Euclidean d,
        (1 + r * ‖ξ‖)^L *
          ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ φ)) ξ‖ ≤ C * r^n

/-- In positive dimension, cancellation removes the possible discrepancy
supported at frequency zero. No physical-kernel hypothesis is needed here. -/
def frequencyReconstructionType : Prop := ∀ (d N : ℕ), 0 < d →
  ∀ (K : KernelDistribution d) (U : Tempered ℂ d) (m : Euclidean d → ℂ),
    BumpCancellation K N → ExtendsKernel U K → BoundedFunction m →
    FourierAgreesOffZero U m → FourierRepresentedBy U m

end Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence
