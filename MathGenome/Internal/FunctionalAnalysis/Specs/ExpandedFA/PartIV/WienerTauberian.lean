import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.WienerDensity
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace ExpandedFA.PartIV.WienerTauberian
open ExpandedFA.Fourier

/-- Ordinary convolution, with no conjugation, evaluated at every point. -/
def convolutionValue {𝕜 G : Type*} [RCLike 𝕜] [Sub G] [MeasureSpace G]
    (f φ : G → 𝕜) (x : G) : 𝕜 := ∫ y, f y * φ (x - y)

/-- Escape to infinity in Euclidean norm, including dimension zero. -/
def infinity (d : ℕ) : Filter (Euclidean d) := comap norm atTop

/-- The real line is represented by its single Euclidean coordinate. -/
def positiveInfinity : Filter (Euclidean 1) := comap (fun x => x 0) atTop

/-- Slow oscillation for the actual representative, as in the manuscript. -/
def SlowOscillation {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} (φ : Euclidean d → 𝕜) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
    ∀ x h : Euclidean d, ‖h‖ < δ → R < ‖x‖ → ‖φ (x-h) - φ x‖ < ε

def SlowOscillationRight {𝕜 : Type*} [RCLike 𝕜] (φ : Euclidean 1 → 𝕜) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
    ∀ x h : Euclidean 1, ‖h‖ < δ → R < x 0 → ‖φ (x-h) - φ x‖ < ε

/-- The standard 2π Fourier convention on the literal real line. -/
def lineFourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ y, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((y * ξ : ℝ) : ℂ)) * f y

def SlowOscillationAtTop {𝕜 : Type*} [RCLike 𝕜] (φ : ℝ → 𝕜) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
    ∀ x h : ℝ, ‖h‖ < δ → R < x → ‖φ (x-h) - φ x‖ < ε

end ExpandedFA.PartIV.WienerTauberian

namespace Specs.ExpandedFA.PartIV.WienerTauberian
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.PartIV.WienerTauberian

/-- Both Tauberian conclusions over complex scalars, for all dimensions. -/
def ComplexTauberian : Prop := ∀ (d : ℕ) (K φ : Euclidean d → ℂ) (a : ℂ),
  Integrable K → MemLp φ ∞ volume → (∀ ξ, integralFourier K ξ ≠ 0) →
  Tendsto (convolutionValue K φ) (infinity d) (𝓝 (a * ∫ y, K y)) →
  (∀ f : Euclidean d → ℂ, Integrable f →
    Tendsto (convolutionValue f φ) (infinity d) (𝓝 (a * ∫ y, f y))) ∧
  (SlowOscillation φ → Tendsto φ (infinity d) (𝓝 a))

/-- The analogous limit at +infinity on the real line. -/
def ComplexTauberianRight : Prop := ∀ (K φ : Euclidean 1 → ℂ) (a : ℂ),
  Integrable K → MemLp φ ∞ volume → (∀ ξ, integralFourier K ξ ≠ 0) →
  Tendsto (convolutionValue K φ) positiveInfinity (𝓝 (a * ∫ y, K y)) →
  (∀ f : Euclidean 1 → ℂ, Integrable f →
    Tendsto (convolutionValue f φ) positiveInfinity (𝓝 (a * ∫ y, f y))) ∧
  (SlowOscillationRight φ → Tendsto φ positiveInfinity (𝓝 a))

/-- Real scalars use their usual complex-valued Fourier transform. -/
def RealTauberian : Prop := ∀ (d : ℕ) (K φ : Euclidean d → ℝ) (a : ℝ),
  Integrable K → MemLp φ ∞ volume → (∀ ξ, integralFourier (fun x => (K x : ℂ)) ξ ≠ 0) →
  Tendsto (convolutionValue K φ) (infinity d) (𝓝 (a * ∫ y, K y)) →
  (∀ f : Euclidean d → ℝ, Integrable f →
    Tendsto (convolutionValue f φ) (infinity d) (𝓝 (a * ∫ y, f y))) ∧
  (SlowOscillation φ → Tendsto φ (infinity d) (𝓝 a))

def RealTauberianRight : Prop := ∀ (K φ : Euclidean 1 → ℝ) (a : ℝ),
  Integrable K → MemLp φ ∞ volume → (∀ ξ, integralFourier (fun x => (K x : ℂ)) ξ ≠ 0) →
  Tendsto (convolutionValue K φ) positiveInfinity (𝓝 (a * ∫ y, K y)) →
  (∀ f : Euclidean 1 → ℝ, Integrable f →
    Tendsto (convolutionValue f φ) positiveInfinity (𝓝 (a * ∫ y, f y))) ∧
  (SlowOscillationRight φ → Tendsto φ positiveInfinity (𝓝 a))

/-- The one-sided theorem also presented on the literal real line. -/
def ComplexLineTauberian : Prop := ∀ (K φ : ℝ → ℂ) (a : ℂ),
  Integrable K → MemLp φ ∞ volume → (∀ ξ, lineFourier K ξ ≠ 0) →
  Tendsto (convolutionValue K φ) atTop (𝓝 (a * ∫ y, K y)) →
  (∀ f : ℝ → ℂ, Integrable f →
    Tendsto (convolutionValue f φ) atTop (𝓝 (a * ∫ y, f y))) ∧
  (SlowOscillationAtTop φ → Tendsto φ atTop (𝓝 a))

def RealLineTauberian : Prop := ∀ (K φ : ℝ → ℝ) (a : ℝ),
  Integrable K → MemLp φ ∞ volume → (∀ ξ, lineFourier (fun x => (K x : ℂ)) ξ ≠ 0) →
  Tendsto (convolutionValue K φ) atTop (𝓝 (a * ∫ y, K y)) →
  (∀ f : ℝ → ℝ, Integrable f →
    Tendsto (convolutionValue f φ) atTop (𝓝 (a * ∫ y, f y))) ∧
  (SlowOscillationAtTop φ → Tendsto φ atTop (𝓝 a))

end Specs.ExpandedFA.PartIV.WienerTauberian
