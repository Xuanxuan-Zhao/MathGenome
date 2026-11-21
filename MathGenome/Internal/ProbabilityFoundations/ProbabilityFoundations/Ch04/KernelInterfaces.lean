import Mathlib.Probability.Kernel.Basic

/-!
The definition in §4.2 of the manuscript, for arbitrary specified measurable spaces.
A probability kernel is precisely a Mathlib `Kernel` with `IsMarkovKernel`.
No topology, countable generation, or nonemptiness is required.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch04

universe u v
variable {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]

/-- The manuscript's two conditions on a measure-valued family. -/
def IsProbabilityKernelFamily (f : S → Measure T) : Prop :=
  (∀ s, IsProbabilityMeasure (f s)) ∧
    ∀ B : Set T, MeasurableSet B → Measurable (fun s => f s B)

/-- Construct a Mathlib kernel from exactly the manuscript's family conditions. -/
def kernelOfFamily (f : S → Measure T) (hf : IsProbabilityKernelFamily f) : Kernel S T where
  toFun := f
  measurable' := Measure.measurable_of_measurable_coe f hf.2

instance kernelOfFamily_isMarkovKernel (f : S → Measure T)
    (hf : IsProbabilityKernelFamily f) : IsMarkovKernel (kernelOfFamily f hf) :=
  ⟨hf.1⟩

@[simp] theorem kernelOfFamily_apply (f : S → Measure T)
    (hf : IsProbabilityKernelFamily f) (s : S) : kernelOfFamily f hf s = f s := rfl

/-- The identification with `IsMarkovKernel` has no extra assumptions. -/
theorem isMarkovKernel_iff_family (K : Kernel S T) :
    IsMarkovKernel K ↔ IsProbabilityKernelFamily (fun s => K s) := by
  constructor
  · intro h
    exact ⟨h.isProbabilityMeasure, fun B hB => K.measurable_coe hB⟩
  · intro h
    exact ⟨h.1⟩

/-- Every family in the source definition, and only such a family, is represented
by a Markov kernel, with equality of the whole measure at each point. -/
theorem family_iff_exists_kernel (f : S → Measure T) :
    IsProbabilityKernelFamily f ↔
      ∃ K : Kernel S T, IsMarkovKernel K ∧ ∀ s, K s = f s := by
  constructor
  · intro hf
    exact ⟨kernelOfFamily f hf, inferInstance, fun _ => rfl⟩
  · rintro ⟨K, hK, h⟩
    have hf : (fun s => K s) = f := funext h
    rw [← hf]
    exact (isMarkovKernel_iff_family K).mp hK

/-- Evaluations are measurable on every measurable target set. -/
theorem kernel_measurable_eval (K : Kernel S T) (B : Set T) (hB : MeasurableSet B) :
    Measurable (fun s => K s B) := K.measurable_coe hB

/-- A probability kernel gives a probability measure at every point. -/
theorem kernel_isProbabilityMeasure (K : Kernel S T) [IsMarkovKernel K] (s : S) :
    IsProbabilityMeasure (K s) := inferInstance

@[simp] theorem kernel_univ (K : Kernel S T) [IsMarkovKernel K] (s : S) :
    K s Set.univ = 1 := measure_univ

/-- The identity kernel `I_S(s, ·) = δ_s`. -/
noncomputable def identityKernel (S : Type u) [MeasurableSpace S] : Kernel S S := Kernel.id

instance identityKernel_isMarkovKernel (S : Type u) [MeasurableSpace S] :
    IsMarkovKernel (identityKernel S) := by
  unfold identityKernel
  infer_instance

@[simp] theorem identityKernel_apply (s : S) :
    identityKernel S s = Measure.dirac s := Kernel.id_apply s

/-- The point-membership formula requires only measurability of the evaluated set,
not measurable singletons. -/
theorem identityKernel_eval (s : S) (B : Set S) (hB : MeasurableSet B)
    [Decidable (s ∈ B)] : identityKernel S s B = if s ∈ B then 1 else 0 := by
  rw [identityKernel_apply, Measure.dirac_apply' s hB]
  exact Set.indicator_apply B (fun _ => (1 : ℝ≥0∞)) s

@[simp] theorem identityKernel_univ (s : S) : identityKernel S s Set.univ = 1 :=
  kernel_univ _ s

end ProbabilityFoundations.Ch04
