import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelMeasure

/-!
Independent statements for the integration assertions of `thm:kernel-measure`,
`paper.tex` §4.2. Both state spaces have arbitrary specified sigma algebras.
`ℝ≥0∞` permits infinite nonnegative integrals. For real functions, finiteness
of the absolute fiber integral is expressed using `ENNReal.ofReal |f|`.
The final statement quantifies over every measurable extension agreeing with
the true signed integral at every point where the fiber is integrable.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch04.KernelIntegration

universe u v

def kernel_lintegral_measurable_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (K : Kernel S T) [IsMarkovKernel K] (f : S × T → ℝ≥0∞),
    Measurable f → Measurable (fun s => ∫⁻ y, f (s, y) ∂K s)

def kernel_lintegral_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K]
    (f : S × T → ℝ≥0∞), Measurable f →
    ∫⁻ z, f z ∂KernelMeasure.kernelMeasureValue μ K =
      ∫⁻ s, ∫⁻ y, f (s, y) ∂K s ∂μ

def kernel_integral_measurable_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (K : Kernel S T) [IsMarkovKernel K] (f : S × T → ℝ),
    Measurable f → Measurable (fun s => ∫ y, f (s, y) ∂K s)

def kernel_ae_integrable_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K]
    (f : S × T → ℝ), Measurable f →
    Integrable f (KernelMeasure.kernelMeasureValue μ K) →
    ∀ᵐ s ∂μ, Integrable (fun y => f (s, y)) (K s) ∧
      (∫⁻ y, ENNReal.ofReal |f (s, y)| ∂K s) < ∞

def kernel_integral_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K]
    (f : S × T → ℝ), Measurable f →
    Integrable f (KernelMeasure.kernelMeasureValue μ K) →
    Integrable (fun s => ∫ y, f (s, y) ∂K s) μ ∧
      (∫ z, f z ∂KernelMeasure.kernelMeasureValue μ K) =
        ∫ s, ∫ y, f (s, y) ∂K s ∂μ

def kernel_integral_extension_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K]
    (f : S × T → ℝ), Measurable f →
    Integrable f (KernelMeasure.kernelMeasureValue μ K) →
    ∀ (g : S → ℝ), Measurable g →
    (∀ s, Integrable (fun y => f (s, y)) (K s) → g s = ∫ y, f (s, y) ∂K s) →
    Integrable g μ ∧ (∫ z, f z ∂KernelMeasure.kernelMeasureValue μ K) = ∫ s, g s ∂μ

end Specs.ProbabilityFoundations.Ch04.KernelIntegration
