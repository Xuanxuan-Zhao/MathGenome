import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelInterfaces

/-!
The measure induced by a probability kernel, for arbitrary measurable spaces.
This is the construction and first marginal in `thm:kernel-measure` of §4.2.
Mathlib's `Measure.compProd` is the source's `μ ⊗ K`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch04

universe u v
variable {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]

/-- Every section of a product-measurable set is measurable, at every base point. -/
theorem kernel_section_measurable (C : Set (S × T)) (hC : MeasurableSet C) (s : S) :
    MeasurableSet {y : T | (s, y) ∈ C} :=
  measurable_prodMk_left hC

/-- Measurability of the moving section evaluated by the probability kernel. -/
theorem kernel_section_eval_measurable (K : Kernel S T) [IsMarkovKernel K]
    (C : Set (S × T)) (hC : MeasurableSet C) :
    Measurable (fun s => K s {y : T | (s, y) ∈ C}) :=
  Kernel.measurable_kernel_prodMk_left hC

/-- The measure on the product sigma-algebra induced by `μ` and `K`. -/
noncomputable def kernelMeasure (μ : Measure S) (K : Kernel S T) : Measure (S × T) :=
  μ.compProd K

/-- The defining section-integral formula on every product-measurable set. -/
theorem kernelMeasure_apply (μ : Measure S) [IsProbabilityMeasure μ]
    (K : Kernel S T) [IsMarkovKernel K] (C : Set (S × T)) (hC : MeasurableSet C) :
    kernelMeasure μ K C = ∫⁻ s, K s {y : T | (s, y) ∈ C} ∂μ :=
  Measure.compProd_apply hC

/-- Countable additivity is built into the measure; its total mass is one. -/
instance kernelMeasure_isProbabilityMeasure (μ : Measure S) [IsProbabilityMeasure μ]
    (K : Kernel S T) [IsMarkovKernel K] : IsProbabilityMeasure (kernelMeasure μ K) := by
  unfold kernelMeasure
  infer_instance

/-- Pushing the induced measure forward by the first projection recovers `μ`. -/
@[simp] theorem kernelMeasure_fst (μ : Measure S) [IsProbabilityMeasure μ]
    (K : Kernel S T) [IsMarkovKernel K] : (kernelMeasure μ K).map Prod.fst = μ :=
  Measure.fst_compProd μ K

end ProbabilityFoundations.Ch04
