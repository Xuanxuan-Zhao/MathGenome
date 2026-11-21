import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelIntegration

/-!
Composition and common-source product of probability kernels, paper.tex §4.2.
Mathlib composition uses reverse argument order, so `kernelComposition K L`
is `L ∘ₖ K`. All results retain arbitrary measurable state spaces.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch04

universe u v w x

noncomputable def kernelComposition {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) (L : Kernel T U) : Kernel S U := L ∘ₖ K

noncomputable def productKernel {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) (L : Kernel S U) : Kernel S (T × U) := K ×ₖ L

instance kernelComposition_isMarkovKernel {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L] :
    IsMarkovKernel (kernelComposition K L) := by
  unfold kernelComposition
  infer_instance

theorem kernelComposition_apply {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (C : Set U) (hC : MeasurableSet C) :
    kernelComposition K L s C = ∫⁻ y, L y C ∂K s :=
  Kernel.comp_apply' L K s hC

theorem kernelComposition_eval_measurable {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (C : Set U) (hC : MeasurableSet C) :
    Measurable (fun s => kernelComposition K L s C) :=
  (kernelComposition K L).measurable_coe hC

theorem kernelComposition_lintegral_measurable {T : Type v} {U : Type w} [MeasurableSpace T] [MeasurableSpace U]
    (L : Kernel T U) [IsMarkovKernel L] (h : U → ℝ≥0∞) (hh : Measurable h) :
    Measurable (fun y => ∫⁻ z, h z ∂L y) := hh.lintegral_kernel

theorem kernelComposition_lintegral {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (h : U → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ z, h z ∂kernelComposition K L s) = ∫⁻ y, ∫⁻ z, h z ∂L y ∂K s :=
  Kernel.lintegral_comp L K s hh

theorem kernelComposition_integral_measurable {T : Type v} {U : Type w} [MeasurableSpace T] [MeasurableSpace U]
    (L : Kernel T U) [IsMarkovKernel L] (h : U → ℝ) (hh : Measurable h) :
    Measurable (fun y => ∫ z, h z ∂L y) :=
  hh.stronglyMeasurable.integral_kernel.measurable

theorem kernelComposition_ae_integrable {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (h : U → ℝ)
    (hi : Integrable h (kernelComposition K L s)) :
    ∀ᵐ y ∂K s, Integrable h (L y) ∧ (∫⁻ z, ENNReal.ofReal |h z| ∂L y) < ∞ := by
  have ha : ∀ᵐ y ∂K s, Integrable h (L y) := hi.ae_of_comp
  filter_upwards [ha] with y hy
  exact ⟨hy, by simpa only [Real.norm_eq_abs] using
    (hasFiniteIntegral_iff_norm _).mp hy.hasFiniteIntegral⟩

theorem kernelComposition_integral {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (h : U → ℝ)
    (hi : Integrable h (kernelComposition K L s)) :
    Integrable (fun y => ∫ z, h z ∂L y) (K s) ∧
      (∫ z, h z ∂kernelComposition K L s) = ∫ y, ∫ z, h z ∂L y ∂K s :=
  ⟨hi.integral_comp, Kernel.integral_comp hi⟩

theorem kernelComposition_integral_extension {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (h : U → ℝ)
    (hi : Integrable h (kernelComposition K L s))
    (g : T → ℝ) (_hg : Measurable g)
    (hgh : ∀ y, Integrable h (L y) → g y = ∫ z, h z ∂L y) :
    Integrable g (K s) ∧ (∫ z, h z ∂kernelComposition K L s) = ∫ y, g y ∂K s := by
  have heq : g =ᵐ[K s] (fun y => ∫ z, h z ∂L y) := by
    filter_upwards [kernelComposition_ae_integrable K L s h hi] with y hy
    exact hgh y hy.1
  have hs := kernelComposition_integral K L s h hi
  exact ⟨hs.1.congr heq.symm, hs.2.trans (integral_congr_ae heq.symm)⟩

theorem kernelComposition_assoc {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    {V : Type x} [MeasurableSpace V] (M : Kernel U V) [IsMarkovKernel M] :
    kernelComposition (kernelComposition K L) M =
      kernelComposition K (kernelComposition L M) :=
  (Kernel.comp_assoc M L K).symm

theorem identityKernel_composition {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (K : Kernel S T) [IsMarkovKernel K] :
    kernelComposition (identityKernel S) K = K := Kernel.comp_id K

theorem composition_identityKernel {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (K : Kernel S T) [IsMarkovKernel K] :
    kernelComposition K (identityKernel T) = K := Kernel.id_comp K

instance productKernel_isMarkovKernel {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel S U) [IsMarkovKernel L] :
    IsMarkovKernel (productKernel K L) := by
  unfold productKernel
  infer_instance

theorem productKernel_apply {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel S U) [IsMarkovKernel L]
    (s : S) :
    productKernel K L s = (K s).prod (L s) := Kernel.prod_apply K L s

theorem productKernel_eval_measurable {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel S U) [IsMarkovKernel L]
    (C : Set (T × U)) (hC : MeasurableSet C) :
    Measurable (fun s => (K s).prod (L s) C) := by
  simpa only [← productKernel_apply K L] using (productKernel K L).measurable_coe hC

theorem productKernel_apply_rectangle {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel S U) [IsMarkovKernel L]
    (s : S) (B : Set T) (C : Set U) :
    productKernel K L s (B ×ˢ C) = K s B * L s C := Kernel.prod_apply_prod

end ProbabilityFoundations.Ch04
