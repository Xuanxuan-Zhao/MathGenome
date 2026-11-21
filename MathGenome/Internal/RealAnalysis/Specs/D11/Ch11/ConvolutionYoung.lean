import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ConvolutionBound

/-! Young's theorem (paper.tex:3704–3730). The bound and independence are the
upstream assertions in full. The additional algebra laws use native `Lp`, whose
identification with the ordinary measurable a.e. quotient is established in
Ch10.QuotientConstruction; no local-null quotient is used.

`l1Convolution_value` takes the class of the same zero-extended integral as the
upstream definition. Its fallback is made unreachable by the representative
and membership assertion, rather than assumed in the definition. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Specs.D11.Ch11.ConvolutionYoung
open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch11.ConvolutionBound (convolution_value)

def young : Prop := Specs.D11.Ch11.ConvolutionBound.young
def representative_independence : Prop := Specs.D11.Ch11.ConvolutionBound.representative_independence
def quotient_bound : Prop := Specs.D11.Ch11.ConvolutionBound.quotient_bound
def quotient_independence : Prop := Specs.D11.Ch11.ConvolutionBound.quotient_independence

def l1Convolution_type := ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜],
  letI := lebesgueSpace_value d
  Lp 𝕜 1 (lebesgue_value d) → Lp 𝕜 1 (lebesgue_value d) → Lp 𝕜 1 (lebesgue_value d)

def l1Convolution_value : l1Convolution_type := by
  classical
  exact fun d _ 𝕜 _ k f =>
    if h : MemLp (convolution_value d (k : Point d → 𝕜) (f : Point d → 𝕜)) 1
        (lebesgue_value d)
    then h.toLp (convolution_value d (k : Point d → 𝕜) (f : Point d → 𝕜))
    else 0

/-- All measurable L1 representatives yield this same class, and the integrals
used to represent it are absolutely convergent almost everywhere. -/
def l1_representatives : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    letI := lebesgueSpace_value d
    ∀ (k f : Point d → 𝕜), Measurable k → Measurable f →
    ∀ (hk : MemLp k 1 (lebesgue_value d)) (hf : MemLp f 1 (lebesgue_value d)),
    (∀ᵐ x ∂lebesgue_value d, Integrable (fun y => k y * f (x-y)) (lebesgue_value d)) ∧
    Measurable (convolution_value d k f) ∧
    ∃ hc : MemLp (convolution_value d k f) 1 (lebesgue_value d),
      l1Convolution_value d 𝕜 (hk.toLp k) (hf.toLp f) = hc.toLp (convolution_value d k f)

/-- Bilinearity, commutativity and associativity on actual ordinary a.e. classes. -/
def l1_algebra : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    letI := lebesgueSpace_value d
    let C := l1Convolution_value d 𝕜
    ∀ k f g : Lp 𝕜 1 (lebesgue_value d),
      C (k+f) g = C k g + C f g ∧
      C k (f+g) = C k f + C k g ∧
      (∀ c : 𝕜, C (c • k) f = c • C k f) ∧
      (∀ c : 𝕜, C k (c • f) = c • C k f) ∧
      C k f = C f k ∧
      C (C k f) g = C k (C f g) ∧
      ‖C k f‖ ≤ ‖k‖ * ‖f‖

end Specs.D11.Ch11.ConvolutionYoung
