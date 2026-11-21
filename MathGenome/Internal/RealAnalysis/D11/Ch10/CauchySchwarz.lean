import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.CauchySchwarz
import MathGenome.Internal.RealAnalysis.D11.Ch10.Holder
import MathGenome.Internal.RealAnalysis.D11.Ch06.LinearityOrder

/-! Cauchy–Schwarz (paper.tex:3334–3343) for both real and complex scalars
on an arbitrary positive measure space, with the original measurable
representatives. Hölder at (2,2) proves the product assertion. Conjugation
preserves the raw square norm, so the scalar absolute-value bound gives
the conjugate-pairing assertion.
-/
open Set MeasureTheory
open scoped ENNReal ComplexConjugate
universe u
noncomputable section
namespace D11.Ch10.CauchySchwarz
open LpDefinition D11.Ch05.NonnegativeIntegral D11.Ch06.ScalarIntegral

theorem product_bound : Specs.D11.Ch10.CauchySchwarz.product_bound := by
  intro X 𝕜 _ _ _ _ μ f g hf hg
  exact Holder.holder_finite μ 2 2 f g (by constructor <;> norm_num) hf hg

theorem integral_bound : Specs.D11.Ch10.CauchySchwarz.integral_bound := by
  intro X 𝕜 _ _ _ _ μ f g hf hg
  change f ∈ rawLp μ 2 at hf
  change g ∈ rawLp μ 2 at hg
  have hnorm : powerNorm μ 2 (fun x => conj (g x)) = powerNorm μ 2 g := by
    simp only [powerNorm, RCLike.norm_conj]
  have hgc : (fun x => conj (g x)) ∈ rawLp μ 2 :=
    ⟨RCLike.continuous_conj.measurable.comp hg.1, hnorm ▸ hg.2⟩
  obtain ⟨hi, hb⟩ := product_bound μ f (fun x => conj (g x)) hf hgc
  change nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x * conj (g x)‖) ≤
    powerNorm μ 2 f * powerNorm μ 2 (fun x => conj (g x)) at hb
  refine ⟨hi, ?_⟩
  have hb' : nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x * conj (g x)‖) ≤
      powerNorm μ 2 f * powerNorm μ 2 g := by
    simpa only [hnorm] using hb
  calc
    _ ≤ (nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x * conj (g x)‖)).toReal :=
      D11.Ch06.LinearityOrder.absolute_value_bound μ _ hi
    _ ≤ (powerNorm μ 2 f * powerNorm μ 2 g).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top hf.2.ne hg.2.ne) hb'
    _ = _ := ENNReal.toReal_mul

end D11.Ch10.CauchySchwarz
