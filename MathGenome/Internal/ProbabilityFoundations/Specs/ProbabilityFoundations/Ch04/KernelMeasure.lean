import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelInterfaces

/-!
Independent specification of the measure-construction part of
`paper.tex`, Theorem `thm:kernel-measure` (§4.2, lines 1120–1125).
The product carries the product of the specified measurable structures.
Sections are the literal sets `{y | (s, y) ∈ C}`. No topological,
standard Borel, countability, completeness or nonemptiness assumptions occur.
The nonnegative integral uses Mathlib's extended-nonnegative measure values.
The subsequent integration assertions belong to the separate integration goal.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch04.KernelMeasure

universe u v

/-- The usual composition product identifies the source's induced measure. -/
noncomputable def kernelMeasureValue {S : Type u} {T : Type v}
    [MeasurableSpace S] [MeasurableSpace T] (μ : Measure S) (K : Kernel S T) :
    Measure (S × T) := μ.compProd K

def kernel_section_measurable_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (C : Set (S × T)), MeasurableSet C →
    ∀ s : S, MeasurableSet {y : T | (s, y) ∈ C}

def kernel_section_eval_measurable_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (K : Kernel S T) [IsMarkovKernel K] (C : Set (S × T)),
    MeasurableSet C → Measurable (fun s => K s {y : T | (s, y) ∈ C})

def kernelMeasure_type : Type _ :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
    Measure S → Kernel S T → Measure (S × T)

def kernelMeasure_apply_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K]
    (C : Set (S × T)), MeasurableSet C →
    kernelMeasureValue μ K C = ∫⁻ s, K s {y : T | (s, y) ∈ C} ∂μ

def kernelMeasure_isProbabilityMeasure_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K],
    IsProbabilityMeasure (kernelMeasureValue μ K)

def kernelMeasure_fst_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K],
    (kernelMeasureValue μ K).map Prod.fst = μ

end Specs.ProbabilityFoundations.Ch04.KernelMeasure
