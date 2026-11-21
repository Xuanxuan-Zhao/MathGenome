import Mathlib.Probability.Kernel.Basic

/-!
Independent specification of the probability-kernel definition in paper.tex §4.2.
All spaces carry arbitrary specified sigma algebras. Evaluations take values in
`ℝ≥0∞`, as in Mathlib's measure interface. There are no topological or
nonemptiness hypotheses. The value definitions specify the two conditions,
the family constructor, and the Dirac identity independently of the candidate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch04.KernelInterfaces

universe u v

/-- Exactly the two conditions in the source definition. -/
def familyValue {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (f : S → Measure T) : Prop :=
  (∀ s, IsProbabilityMeasure (f s)) ∧
    ∀ B : Set T, MeasurableSet B → Measurable (fun s => f s B)

/-- The prescribed kernel keeps the entire supplied measure-valued family. -/
def kernelOfFamilyValue {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (f : S → Measure T) (hf : familyValue f) : Kernel S T where
  toFun := f
  measurable' := Measure.measurable_of_measurable_coe f hf.2

/-- The source identity is Mathlib's identity kernel. -/
noncomputable def identityKernelValue (S : Type u) [MeasurableSpace S] : Kernel S S :=
  Kernel.id

def IsProbabilityKernelFamily_type : Type _ :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
  (S → Measure T) → Prop

def kernelOfFamily_type : Type _ :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
  ∀ (f : S → Measure T), familyValue f → Kernel S T

def kernelOfFamily_isMarkovKernel_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
  ∀ (f : S → Measure T) (hf : familyValue f),
    IsMarkovKernel (kernelOfFamilyValue f hf)

def kernelOfFamily_apply_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
  ∀ (f : S → Measure T) (hf : familyValue f) (s : S),
    kernelOfFamilyValue f hf s = f s

def isMarkovKernel_iff_family_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
  ∀ (K : Kernel S T),
    IsMarkovKernel K ↔ familyValue (fun s => K s)

def family_iff_exists_kernel_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
  ∀ (f : S → Measure T),
    familyValue f ↔ ∃ K : Kernel S T, IsMarkovKernel K ∧ ∀ s, K s = f s

def kernel_measurable_eval_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
  ∀ (K : Kernel S T) (B : Set T), MeasurableSet B →
    Measurable (fun s => K s B)

def kernel_isProbabilityMeasure_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
  ∀ (K : Kernel S T) [IsMarkovKernel K] (s : S),
    IsProbabilityMeasure (K s)

def kernel_univ_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T],
  ∀ (K : Kernel S T) [IsMarkovKernel K] (s : S),
    K s Set.univ = 1

def identityKernel_type : Type _ :=
  ∀ (S : Type u) [MeasurableSpace S],
  Kernel S S

def identityKernel_isMarkovKernel_type : Prop :=
  ∀ (S : Type u) [MeasurableSpace S],
  IsMarkovKernel (identityKernelValue S)

def identityKernel_apply_type : Prop :=
  ∀ {S : Type u} [MeasurableSpace S],
  ∀ (s : S), identityKernelValue S s = Measure.dirac s

def identityKernel_eval_type : Prop :=
  ∀ {S : Type u} [MeasurableSpace S],
  ∀ (s : S) (B : Set S), MeasurableSet B →
    ∀ [Decidable (s ∈ B)], identityKernelValue S s B = if s ∈ B then 1 else 0

def identityKernel_univ_type : Prop :=
  ∀ {S : Type u} [MeasurableSpace S],
  ∀ (s : S), identityKernelValue S s Set.univ = 1

end Specs.ProbabilityFoundations.Ch04.KernelInterfaces
