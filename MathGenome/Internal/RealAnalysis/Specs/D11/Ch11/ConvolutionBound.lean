import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Young's L¹ × Lᵖ bound, paper.tex:3704–3730, excluding the separately
allocated commutativity and associativity conclusions. The domain is the full
completed Euclidean Lebesgue space. `convolution_value` is zero where absolute
integrability fails; all uses as a linear integral carry integrability proofs.
The upstream ordinary quotient and norm bridge identify native MemLp/eLpNorm
with the source Lp spaces, including the essential-supremum endpoint. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Specs.D11.Ch11.ConvolutionBound
open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures

def convolution_type := ∀ (d : ℕ) [NeZero d] {𝕜 : Type} [RCLike 𝕜],
  (Point d → 𝕜) → (Point d → 𝕜) → Point d → 𝕜

def convolution_value : convolution_type := fun d _ _ _ k f x =>
  letI := lebesgueSpace_value d
  ∫ y, k y * f (x - y) ∂lebesgue_value d

def young : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞), 1 ≤ p →
    letI := lebesgueSpace_value d
    ∀ (k f : Point d → 𝕜), Measurable k → Measurable f →
      MemLp k 1 (lebesgue_value d) → MemLp f p (lebesgue_value d) →
      (∀ᵐ x ∂lebesgue_value d, Integrable (fun y => k y * f (x-y)) (lebesgue_value d)) ∧
      Measurable (convolution_value d k f) ∧
      MemLp (convolution_value d k f) p (lebesgue_value d) ∧
      eLpNorm (convolution_value d k f) p (lebesgue_value d) ≤
        eLpNorm k 1 (lebesgue_value d) * eLpNorm f p (lebesgue_value d)

def zero_extension : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜] (k f : Point d → 𝕜) (x : Point d),
    letI := lebesgueSpace_value d
    ¬ Integrable (fun y => k y * f (x-y)) (lebesgue_value d) →
      convolution_value d k f x = 0

/-- Stronger than a.e. independence: both the existence set and the zero-extended
integral agree at every point. In particular their ordinary Lp classes agree. -/
def representative_independence : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜],
    letI := lebesgueSpace_value d
    ∀ (k k' f f' : Point d → 𝕜), k =ᵐ[lebesgue_value d] k' →
      f =ᵐ[lebesgue_value d] f' →
      (∀ x, Integrable (fun y => k y * f (x-y)) (lebesgue_value d) ↔
        Integrable (fun y => k' y * f' (x-y)) (lebesgue_value d)) ∧
      convolution_value d k f = convolution_value d k' f'

/-- Pointwise bilinearity on the common absolute-existence domain. -/
def bilinearity : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜],
    letI := lebesgueSpace_value d
    ∀ (k k' f f' : Point d → 𝕜) (x : Point d),
      (Integrable (fun y => k y * f (x-y)) (lebesgue_value d) →
       Integrable (fun y => k' y * f (x-y)) (lebesgue_value d) →
       convolution_value d (k+k') f x = convolution_value d k f x + convolution_value d k' f x) ∧
      (Integrable (fun y => k y * f (x-y)) (lebesgue_value d) →
       Integrable (fun y => k y * f' (x-y)) (lebesgue_value d) →
       convolution_value d k (f+f') x = convolution_value d k f x + convolution_value d k f' x) ∧
      (∀ c : 𝕜, convolution_value d (c • k) f x = c * convolution_value d k f x) ∧
      (∀ c : 𝕜, convolution_value d k (c • f) x = c * convolution_value d k f x)

/-- The same quantitative bound on the ordinary scalar a.e. quotient. -/
def quotient_bound : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    letI := lebesgueSpace_value d
    ∀ (k f : Point d → 𝕜), Measurable k → Measurable f →
    ∀ (hk : MemLp k 1 (lebesgue_value d)) (hf : MemLp f p (lebesgue_value d)),
    ∃ hc : MemLp (convolution_value d k f) p (lebesgue_value d),
      ‖hc.toLp (convolution_value d k f)‖ ≤ ‖hk.toLp k‖ * ‖hf.toLp f‖

/-- Equality of either input class preserves the output class, for every
choice of proofs of membership. -/
def quotient_independence : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞),
    letI := lebesgueSpace_value d
    ∀ (k k' f f' : Point d → 𝕜)
      (hk : MemLp k 1 (lebesgue_value d)) (hk' : MemLp k' 1 (lebesgue_value d))
      (hf : MemLp f p (lebesgue_value d)) (hf' : MemLp f' p (lebesgue_value d))
      (hc : MemLp (convolution_value d k f) p (lebesgue_value d))
      (hc' : MemLp (convolution_value d k' f') p (lebesgue_value d)),
      hk.toLp k = hk'.toLp k' → hf.toLp f = hf'.toLp f' →
      hc.toLp (convolution_value d k f) = hc'.toLp (convolution_value d k' f')

end Specs.D11.Ch11.ConvolutionBound
