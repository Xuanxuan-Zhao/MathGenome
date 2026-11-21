import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelInterfaces

/-!
Independent statements for paper.tex §4.2, Proposition `prop:kernel-composition`.
All spaces have their specified sigma-algebras, without topological assumptions.
Composition is written in the manuscript order: first K, then L.
The real integral is totalized by zero on nonintegrable fibers; the extension
statement permits every measurable assignment on those exceptional fibers.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch04.KernelComposition

universe u v w x

noncomputable def kernelCompositionValue {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) (L : Kernel T U) : Kernel S U := L ∘ₖ K

noncomputable def productKernelValue {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) (L : Kernel S U) : Kernel S (T × U) := K ×ₖ L

def kernelComposition_type : Type _ :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U], Kernel S T → Kernel T U → Kernel S U

def productKernel_type : Type _ :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U], Kernel S T → Kernel S U → Kernel S (T × U)

def kernelComposition_isMarkovKernel_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L],
    IsMarkovKernel (kernelCompositionValue K L)

def kernelComposition_apply_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (C : Set U) (_hC : MeasurableSet C),
    kernelCompositionValue K L s C = ∫⁻ y, L y C ∂K s

def kernelComposition_eval_measurable_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (C : Set U) (_hC : MeasurableSet C),
    Measurable (fun s => kernelCompositionValue K L s C)

def kernelComposition_lintegral_measurable_type : Prop :=
  ∀ {T : Type v} {U : Type w} [MeasurableSpace T] [MeasurableSpace U]
    (L : Kernel T U) [IsMarkovKernel L] (h : U → ℝ≥0∞) (_hh : Measurable h),
    Measurable (fun y => ∫⁻ z, h z ∂L y)

def kernelComposition_lintegral_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (h : U → ℝ≥0∞) (_hh : Measurable h),
    (∫⁻ z, h z ∂kernelCompositionValue K L s) = ∫⁻ y, ∫⁻ z, h z ∂L y ∂K s

def kernelComposition_integral_measurable_type : Prop :=
  ∀ {T : Type v} {U : Type w} [MeasurableSpace T] [MeasurableSpace U]
    (L : Kernel T U) [IsMarkovKernel L] (h : U → ℝ) (_hh : Measurable h),
    Measurable (fun y => ∫ z, h z ∂L y)

def kernelComposition_ae_integrable_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (h : U → ℝ)
    (_hi : Integrable h (kernelCompositionValue K L s)),
    ∀ᵐ y ∂K s, Integrable h (L y) ∧ (∫⁻ z, ENNReal.ofReal |h z| ∂L y) < ∞

def kernelComposition_integral_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (h : U → ℝ)
    (_hi : Integrable h (kernelCompositionValue K L s)),
    Integrable (fun y => ∫ z, h z ∂L y) (K s) ∧
      (∫ z, h z ∂kernelCompositionValue K L s) = ∫ y, ∫ z, h z ∂L y ∂K s

def kernelComposition_integral_extension_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    (s : S) (h : U → ℝ)
    (_hi : Integrable h (kernelCompositionValue K L s))
    (g : T → ℝ) (_hg : Measurable g)
    (_hgh : ∀ y, Integrable h (L y) → g y = ∫ z, h z ∂L y),
    Integrable g (K s) ∧ (∫ z, h z ∂kernelCompositionValue K L s) = ∫ y, g y ∂K s

def kernelComposition_assoc_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel T U) [IsMarkovKernel L]
    {V : Type x} [MeasurableSpace V] (M : Kernel U V) [IsMarkovKernel M],
    kernelCompositionValue (kernelCompositionValue K L) M = kernelCompositionValue K (kernelCompositionValue L M)

def identityKernel_composition_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (K : Kernel S T) [IsMarkovKernel K],
    kernelCompositionValue (KernelInterfaces.identityKernelValue S) K = K

def composition_identityKernel_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (K : Kernel S T) [IsMarkovKernel K],
    kernelCompositionValue K (KernelInterfaces.identityKernelValue T) = K

def productKernel_isMarkovKernel_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel S U) [IsMarkovKernel L],
    IsMarkovKernel (productKernelValue K L)

def productKernel_apply_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel S U) [IsMarkovKernel L]
    (s : S),
    productKernelValue K L s = (K s).prod (L s)

def productKernel_eval_measurable_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel S U) [IsMarkovKernel L]
    (C : Set (T × U)) (_hC : MeasurableSet C),
    Measurable (fun s => (K s).prod (L s) C)

def productKernel_apply_rectangle_type : Prop :=
  ∀ {S : Type u} {T : Type v} {U : Type w}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (K : Kernel S T) [IsMarkovKernel K] (L : Kernel S U) [IsMarkovKernel L]
    (s : S) (B : Set T) (C : Set U),
    productKernelValue K L s (B ×ˢ C) = K s B * L s C

end Specs.ProbabilityFoundations.Ch04.KernelComposition
