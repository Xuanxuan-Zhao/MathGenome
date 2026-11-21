import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyMaximalInterfaces

/-!
Independent statements for `fa2:p4:hardy-fixed-maximal`, paper.tex:20001–20032.
The standing chapter hypothesis is d ≥ 1. The atomic space is the upstream
quotient with its atomic norm, and convolution and the supremum are the
literal upstream functions over all positive scales. The extended integral
retains infinite maximal functions. No cancellation is assumed for the input.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.HardyFixedMaximalSpec
open ExpandedFA.Fourier HardyMaximalSpec
open ExpandedFA.Hardy.AtomicHardySpaceSpec

/-- Forward estimate in the genuine atomic norm. -/
def Forward : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ Φ : Euclidean d → 𝕜, IsFixedKernel Φ →
    ∃ C : ℝ, 0 < C ∧ ∀ h : Hardy 𝕜 d,
      (∫⁻ x, radial Φ (EmbeddingValue volume h : Euclidean d → 𝕜) x) ≤
        ENNReal.ofReal C * ENNReal.ofReal ‖h‖

/-- The reverse estimate constructs the original atom quotient representative. -/
def Converse : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ Φ : Euclidean d → 𝕜, IsFixedKernel Φ →
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Euclidean d → 𝕜) (hf : Integrable f),
      (∫⁻ x, radial Φ f x) < ⊤ →
      ∃ h : Hardy 𝕜 d, EmbeddingValue volume h = hf.toL1 f ∧
        ‖h‖ ≤ C * (∫⁻ x, radial Φ f x).toReal

/-- The equivalence and a common constant in both quantitative inequalities.
The estimates apply to every atomic representative of the given L¹ function.
Existence of such a representative expresses membership in atomic H¹. -/
def KernelCharacterization {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Euclidean d → 𝕜) (hf : Integrable f),
      ((∃ h : Hardy 𝕜 d, EmbeddingValue volume h = hf.toL1 f) ↔
        (∫⁻ x, radial Φ f x) < ⊤) ∧
      ∀ h : Hardy 𝕜 d, EmbeddingValue volume h = hf.toL1 f →
        C⁻¹ * ‖h‖ ≤ (∫⁻ x, radial Φ f x).toReal ∧
        (∫⁻ x, radial Φ f x).toReal ≤ C * ‖h‖

/-- The complete L¹ assertion for every fixed kernel of the source class. -/
def Characterization : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ Φ : Euclidean d → 𝕜, IsFixedKernel Φ → KernelCharacterization Φ

/-- Every nonzero-integral Schwartz function satisfies the exact fixed-kernel
hypotheses, including all derivative orders. -/
def SchwartzKernels : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (Φ : Schwartz 𝕜 d),
    (∫ x, Φ x) ≠ 0 → IsFixedKernel (Φ : Euclidean d → 𝕜)

/-- The asserted Schwartz specialization, with the same atomic objects and
quantitative conclusion, rather than an assumed kernel bridge. -/
def SchwartzCharacterization : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ Φ : Schwartz 𝕜 d, (∫ x, Φ x) ≠ 0 →
      KernelCharacterization (Φ : Euclidean d → 𝕜)

/-- Gaussian profiles; positive dilation parameter b includes every heat scale. -/
def gaussian {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (b : ℝ) (x : Euclidean d) : 𝕜 :=
  (Real.exp (-b * ‖x‖ ^ 2) : 𝕜)

/-- The heat kernel at time one; radial dilation t is heat time t². -/
def heatKernel (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (x : Euclidean d) : 𝕜 :=
  ((4 * Real.pi) ^ (-(d : ℝ) / 2) : ℝ) • gaussian (1 / 4) x

/-- The literal slower-decaying Poisson profile. -/
def poissonProfile (d : ℕ) (x : Euclidean d) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ (-((d : ℝ) + 1) / 2)

/-- The source specifies the positive constant by integral-one normalization. -/
def poissonConstant (d : ℕ) : ℝ := (∫ x, poissonProfile d x)⁻¹

def poissonKernel (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (x : Euclidean d) : 𝕜 :=
  (poissonConstant d * poissonProfile d x : ℝ)

def GaussianKernels : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (b : ℝ), 0 < b →
    IsFixedKernel (gaussian (𝕜 := 𝕜) (d := d) b)

def GaussianCharacterization : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ b : ℝ, 0 < b → KernelCharacterization (gaussian (𝕜 := 𝕜) (d := d) b)

def HeatKernelExample : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    (∫ x, heatKernel 𝕜 d x) = 1 ∧ IsFixedKernel (heatKernel 𝕜 d) ∧
      KernelCharacterization (heatKernel 𝕜 d)

def PoissonKernelExample : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    0 < poissonConstant d ∧ (∫ x, poissonKernel 𝕜 d x) = 1 ∧
      IsFixedKernel (poissonKernel 𝕜 d) ∧ KernelCharacterization (poissonKernel 𝕜 d)

/-- y ↦ Φ_t(x-y), as an actual Schwartz test. No test is conjugated. -/
def kernelTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Schwartz 𝕜 d) (t : Scale) (x : Euclidean d) : Schwartz 𝕜 d :=
  (t.val ^ d)⁻¹ •
    (SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean d)
        (Units.mk0 (-t.val⁻¹) (neg_ne_zero.mpr (inv_ne_zero t.property.ne')))))
      (SchwartzMap.compSubConstCLM 𝕜 (-(t.val⁻¹ • x)) Φ)

/-- Convolution is defined here only for Schwartz kernels. -/
def temperedConvolve {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Schwartz 𝕜 d) (u : Tempered 𝕜 d) (t : Scale) (x : Euclidean d) : 𝕜 :=
  u (kernelTest Φ t x)

def temperedRadial {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Schwartz 𝕜 d) (u : Tempered 𝕜 d) (x : Euclidean d) : ℝ≥0∞ :=
  ⨆ t : Scale, ENNReal.ofReal ‖temperedConvolve Φ u t x‖

/-- Equality as scalar-linear distributions, on every Schwartz test. -/
def Represents {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Tempered 𝕜 d) (f : Euclidean d → 𝕜) : Prop :=
  ∀ ψ : Schwartz 𝕜 d, u ψ = ∫ x, ψ x * f x

/-- The maximal condition alone recovers an L¹ function. -/
def TemperedRecovery : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (Φ : Schwartz 𝕜 d), (∫ x, Φ x) ≠ 0 →
    ∀ u : Tempered 𝕜 d, (∫⁻ x, temperedRadial Φ u x) < ⊤ →
      ∃ f : Euclidean d → 𝕜, Integrable f ∧ Represents u f

/-- The same atomic equivalence and norm estimates for arbitrary tempered inputs. -/
def TemperedCharacterization : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ Φ : Schwartz 𝕜 d, (∫ x, Φ x) ≠ 0 →
    ∃ C : ℝ, 0 < C ∧ ∀ u : Tempered 𝕜 d,
      ((∃ h : Hardy 𝕜 d, Represents u (EmbeddingValue volume h : Euclidean d → 𝕜)) ↔
        (∫⁻ x, temperedRadial Φ u x) < ⊤) ∧
      ∀ h : Hardy 𝕜 d, Represents u (EmbeddingValue volume h : Euclidean d → 𝕜) →
        C⁻¹ * ‖h‖ ≤ (∫⁻ x, temperedRadial Φ u x).toReal ∧
        (∫⁻ x, temperedRadial Φ u x).toReal ≤ C * ‖h‖

/-- Analytic regularization facts needed by the recovery argument. -/
def TemperedRegularization : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (Φ : Schwartz 𝕜 d) (u : Tempered 𝕜 d),
      (∀ t : Scale, Continuous (temperedConvolve Φ u t)) ∧
      ∀ ψ : Schwartz 𝕜 d,
        Tendsto (fun n : ℕ => ∫ x, ψ x *
          temperedConvolve Φ u ⟨((n : ℝ)+1)⁻¹, by positivity⟩ x) atTop
            (𝓝 ((∫ x, Φ x) * u ψ))


end ExpandedFA.PartIV.HardyFixedMaximalSpec
