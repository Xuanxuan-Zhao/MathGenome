import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelMeasure

/-!
Kernel Tonelli and Fubini for arbitrary measurable state spaces (paper.tex §4.2,
`thm:kernel-measure`). The Bochner integral supplies a canonical measurable
extension, assigning zero to nonintegrable fibers. Any other measurable extension
from the integrability set has the same outer integral.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch04

universe u v
variable {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]

/-- Nonnegative parameter integration is pointwise measurable. -/
theorem kernel_lintegral_measurable (K : Kernel S T) [IsMarkovKernel K]
    (f : S × T → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun s => ∫⁻ y, f (s, y) ∂K s) :=
  hf.lintegral_kernel_prod_right'

/-- Tonelli's identity, including infinite integrals. -/
theorem kernel_lintegral (μ : Measure S) [IsProbabilityMeasure μ]
    (K : Kernel S T) [IsMarkovKernel K] (f : S × T → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂kernelMeasure μ K = ∫⁻ s, ∫⁻ y, f (s, y) ∂K s ∂μ :=
  Measure.lintegral_compProd hf

/-- The totalized signed integral gives a measurable extension on all of `S`. -/
theorem kernel_integral_measurable (K : Kernel S T) [IsMarkovKernel K]
    (f : S × T → ℝ) (hf : Measurable f) :
    Measurable (fun s => ∫ y, f (s, y) ∂K s) :=
  hf.stronglyMeasurable.integral_kernel_prod_right'.measurable

/-- Almost every fiber is integrable and has finite absolute integral. -/
theorem kernel_ae_integrable (μ : Measure S) [IsProbabilityMeasure μ]
    (K : Kernel S T) [IsMarkovKernel K] (f : S × T → ℝ) (_hf : Measurable f)
    (hfi : Integrable f (kernelMeasure μ K)) :
    ∀ᵐ s ∂μ, Integrable (fun y => f (s, y)) (K s) ∧
      (∫⁻ y, ENNReal.ofReal |f (s, y)| ∂K s) < ∞ := by
  have h := (Measure.integrable_compProd_iff hfi.aestronglyMeasurable).mp hfi
  filter_upwards [h.1] with s hs
  exact ⟨hs, by simpa only [Real.norm_eq_abs] using
    (hasFiniteIntegral_iff_norm _).mp hs.hasFiniteIntegral⟩

/-- The signed fiber integral is integrable and satisfies Fubini's identity. -/
theorem kernel_integral (μ : Measure S) [IsProbabilityMeasure μ]
    (K : Kernel S T) [IsMarkovKernel K] (f : S × T → ℝ) (hf : Measurable f)
    (hfi : Integrable f (kernelMeasure μ K)) :
    Integrable (fun s => ∫ y, f (s, y) ∂K s) μ ∧
      (∫ z, f z ∂kernelMeasure μ K) = ∫ s, ∫ y, f (s, y) ∂K s ∂μ := by
  have h := (Measure.integrable_compProd_iff hfi.aestronglyMeasurable).mp hfi
  refine ⟨h.2.mono' (kernel_integral_measurable K f hf).aestronglyMeasurable ?_,
    Measure.integral_compProd hfi⟩
  exact Filter.Eventually.of_forall fun s => norm_integral_le_integral_norm _

/-- Every measurable extension from the fiber integrability set works. -/
theorem kernel_integral_extension (μ : Measure S) [IsProbabilityMeasure μ]
    (K : Kernel S T) [IsMarkovKernel K] (f : S × T → ℝ) (hf : Measurable f)
    (hfi : Integrable f (kernelMeasure μ K)) (g : S → ℝ) (_hg : Measurable g)
    (hgf : ∀ s, Integrable (fun y => f (s, y)) (K s) → g s = ∫ y, f (s, y) ∂K s) :
    Integrable g μ ∧ (∫ z, f z ∂kernelMeasure μ K) = ∫ s, g s ∂μ := by
  have heq : g =ᵐ[μ] (fun s => ∫ y, f (s, y) ∂K s) := by
    filter_upwards [kernel_ae_integrable μ K f hf hfi] with s hs
    exact hgf s hs.1
  have h := kernel_integral μ K f hf hfi
  exact ⟨h.1.congr heq.symm, h.2.trans (integral_congr_ae heq.symm)⟩

end ProbabilityFoundations.Ch04
