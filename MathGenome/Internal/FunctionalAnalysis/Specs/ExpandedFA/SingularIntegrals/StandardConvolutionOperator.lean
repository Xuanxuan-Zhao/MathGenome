import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.Plancherel
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Independent specification for paper.tex:18242–18270.
The norm on the domain is the Euclidean norm, including in the derivative bound.
All dimensions, and both real and complex scalars, are included. The kernel
identity is imposed only for smooth compactly supported inputs. In particular,
no off-support representation for nonsmooth data is an input assumption. -/

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions Topology

namespace ExpandedFA.SingularIntegrals.StandardConvolution

abbrev Space (d : ℕ) := ExpandedFA.Fourier.Euclidean d
abbrev L2 (𝕜 : Type) [RCLike 𝕜] (d : ℕ) := Lp 𝕜 2 (volume : Measure (Space d))
abbrev Tests (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  TestFunction (⊤ : Opens (Space d)) 𝕜 ⊤
abbrev KernelDistribution (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  Tests 𝕜 d →L[𝕜] 𝕜

/-- Reflection and translation in the Euclidean domain. -/
def reflectedTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 d) (x : Space d) : Tests 𝕜 d where
  toFun y := φ (x - y)
  contDiff' := φ.contDiff.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := φ.hasCompactSupport.comp_isClosedEmbedding
    (Homeomorph.subLeft x).isClosedEmbedding
  tsupport_subset' := subset_univ _

/-- The canonical L² class of a test. -/
def testL2 {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (φ : Tests 𝕜 d) : L2 𝕜 d :=
  (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ

/-- Translation invariance, stated on representatives and hence independent of
any choice of representative for an L² class. -/
def TranslationInvariant {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : L2 𝕜 d →L[𝕜] L2 𝕜 d) : Prop :=
  ∀ (a : Space d) (f g : L2 𝕜 d),
    (g : Space d → 𝕜) =ᵐ[volume] (fun x => f (x - a)) →
    (T g : Space d → 𝕜) =ᵐ[volume] (fun x => T f (x - a))

/-- Euclidean length of the coordinate gradient, for either scalar field. -/
def kernelGradientNorm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k : Space d → 𝕜) (x : Space d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ‖fderiv ℝ k x (ExpandedFA.Fourier.basisVector i)‖ ^ 2)

/-- The source's C¹ standard convolution kernel. Values at the origin are
irrelevant, and neither global integrability nor cancellation of k is assumed. -/
structure StandardKernel (𝕜 : Type) [RCLike 𝕜] (d : ℕ) where
  function : Space d → 𝕜
  contDiff : ContDiffOn ℝ 1 function ({0}ᶜ : Set (Space d))
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  size : ∀ x ≠ 0, ‖function x‖ ≤ constant / ‖x‖ ^ d
  gradient : ∀ x ≠ 0, kernelGradientNorm function x ≤ constant / ‖x‖ ^ (d + 1)

/-- The setting of the standard convolution CZ theorem. `kernel_action` is the
L² distribution-kernel identity on smooth inputs; it is not a representation
hypothesis for arbitrary compactly supported L¹ ∩ L² inputs. -/
structure StandardConvolutionOperator (𝕜 : Type) [RCLike 𝕜] (d : ℕ) where
  operator : L2 𝕜 d →L[𝕜] L2 𝕜 d
  translation_invariant : TranslationInvariant operator
  distribution : KernelDistribution 𝕜 d
  kernel : StandardKernel 𝕜 d
  agrees_off_zero : ∀ φ : Tests 𝕜 d, (0 : Space d) ∉ tsupport φ →
    distribution φ = ∫ x, kernel.function x * φ x
  kernel_action : ∀ φ : Tests 𝕜 d,
    (operator (testL2 φ) : Space d → 𝕜) =ᵐ[volume]
      (fun x => distribution (reflectedTest φ x))

/-- The ordinary off-support integral. Absolute integrability is a separate
conclusion, so the totalized Bochner integral cannot conceal a divergence. -/
def kernelIntegral {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k f : Space d → 𝕜) (x : Space d) : 𝕜 := ∫ y, k (x - y) * f y

/-- Essential compact support, with arbitrary representatives permitted. -/
def SupportedAE {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Space d → 𝕜) (S : Set (Space d)) : Prop :=
  ∀ᵐ x ∂volume, x ∉ S → f x = 0

end ExpandedFA.SingularIntegrals.StandardConvolution

namespace Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator
open _root_.ExpandedFA.SingularIntegrals.StandardConvolution

abbrev settingType := ∀ (𝕜 : Type) [RCLike 𝕜] (_d : ℕ), Type
abbrev settingValue : settingType := StandardConvolutionOperator

def smoothRepresentationType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (T : StandardConvolutionOperator 𝕜 d) (φ : Tests 𝕜 d),
  ∀ᵐ x ∂volume, x ∉ tsupport φ →
    (T.operator (testL2 φ)) x = kernelIntegral T.kernel.function φ x

def absoluteIntegrabilityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (k : StandardKernel 𝕜 d) (f : Space d → 𝕜) (S : Set (Space d)),
  IsCompact S → Integrable f → SupportedAE f S →
  ∀ x ∉ S, Integrable (fun y => k.function (x - y) * f y)

/-- Full off-support representation for compactly supported L¹ ∩ L² data. -/
def offSupportRepresentationType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (T : StandardConvolutionOperator 𝕜 d) (f : Space d → 𝕜) (S : Set (Space d)),
  IsCompact S → Integrable f → ∀ h2 : MemLp f 2, SupportedAE f S →
  ∀ᵐ x ∂volume, x ∉ S →
    (T.operator (h2.toLp f)) x = kernelIntegral T.kernel.function f x

/-- Cancellation in the exact form used for each bad cube. The center c is
arbitrary; in applications it is the cube's center and x is outside its dilation. -/
def cancellationRepresentationType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (T : StandardConvolutionOperator 𝕜 d) (f : Space d → 𝕜) (S : Set (Space d)),
  IsCompact S → Integrable f → ∀ h2 : MemLp f 2, SupportedAE f S →
  (∫ y, f y) = 0 → ∀ c : Space d,
  ∀ᵐ x ∂volume, x ∉ S →
    Integrable (fun y => (T.kernel.function (x - y) - T.kernel.function (x - c)) * f y) ∧
    (T.operator (h2.toLp f)) x =
      ∫ y, (T.kernel.function (x - y) - T.kernel.function (x - c)) * f y

end Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator
