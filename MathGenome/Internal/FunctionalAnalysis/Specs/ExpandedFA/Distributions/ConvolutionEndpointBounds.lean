import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
Independent endpoint convolution specifications for paper.tex:17297–17302.
`Fin d → ℝ` is coordinate Euclidean space with Lebesgue volume; d=0 is included.
The native ordinary a.e. Lp spaces admit all Lebesgue measurable representatives
through `MemLp`/a.e. strong measurability. Multiplication has no conjugation.
The integral is zero on the exceptional set where it fails to exist.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.Distributions.ConvolutionEndpointBoundsSpec

def ConvolutionType := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜],
  ((Fin d → ℝ) → 𝕜) → ((Fin d → ℝ) → 𝕜) → (Fin d → ℝ) → 𝕜

def ConvolutionValue : ConvolutionType := fun f g x => ∫ y, f y * g (x-y)

def RepresentativeIndependence : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f f' g g' : (Fin d → ℝ) → 𝕜), f =ᵐ[volume] f' → g =ᵐ[volume] g' →
    (∀ x, Integrable (fun y => f y * g (x-y)) ↔
      Integrable (fun y => f' y * g' (x-y))) ∧
    ConvolutionValue f g = ConvolutionValue f' g'

/-- Even the zero-extended integral is a Borel measurable function, because
changing either input on a null set leaves every output value unchanged. -/
def ConvolutionMeasurable : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f g : (Fin d → ℝ) → 𝕜), AEStronglyMeasurable f volume →
    AEStronglyMeasurable g volume → Measurable (ConvolutionValue f g)

def L1LpEndpoint : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞), 1 ≤ p →
    ∀ (f g : (Fin d → ℝ) → 𝕜), MemLp f 1 volume → MemLp g p volume →
    (∀ᵐ x ∂volume, Integrable (fun y => f y * g (x-y))) ∧
    AEStronglyMeasurable (ConvolutionValue f g) volume ∧
    MemLp (ConvolutionValue f g) p volume ∧
    eLpNorm (ConvolutionValue f g) p volume ≤ eLpNorm f 1 volume * eLpNorm g p volume

def HolderEndpoint : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (p q : ℝ≥0∞) [p.HolderConjugate q]
    (f g : (Fin d → ℝ) → 𝕜), MemLp f p volume → MemLp g q volume →
    (∀ x, Integrable (fun y => f y * g (x-y))) ∧
    AEStronglyMeasurable (ConvolutionValue f g) volume ∧
    MemLp (ConvolutionValue f g) ∞ volume ∧
    (∀ x, ‖ConvolutionValue f g x‖ₑ ≤ eLpNorm f p volume * eLpNorm g q volume) ∧
    eLpNorm (ConvolutionValue f g) ∞ volume ≤ eLpNorm f p volume * eLpNorm g q volume

/-- The actual ordinary a.e. output class exists uniquely, with its norm bound. -/
def L1LpQuotientBound : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp 𝕜 1 (volume : Measure (Fin d → ℝ))) (g : Lp 𝕜 p volume),
    ∃! h : Lp 𝕜 p volume,
      (h : (Fin d → ℝ) → 𝕜) =ᵐ[volume] ConvolutionValue f g ∧ ‖h‖ ≤ ‖f‖ * ‖g‖

def HolderQuotientBound : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (f : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) (g : Lp 𝕜 q volume),
    ∃! h : Lp 𝕜 ∞ volume,
      (h : (Fin d → ℝ) → 𝕜) =ᵐ[volume] ConvolutionValue f g ∧ ‖h‖ ≤ ‖f‖ * ‖g‖

end ExpandedFA.Distributions.ConvolutionEndpointBoundsSpec
