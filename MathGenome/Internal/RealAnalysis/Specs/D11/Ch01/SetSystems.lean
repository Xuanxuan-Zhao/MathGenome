import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.LiminfLimsup

/-!
Canonical objects for paper.tex, Chapter 1, lines 168–209:
* `MeasureTheory.IsSetAlgebra` is the algebra predicate.
* `MeasurableSpace` and `MeasurableSet` encode sigma-algebras and membership.
* `MeasurableSpace.generateFrom` is generation.
* The standard subtype instance (comap of the inclusion) is the trace sigma-algebra.
* `Filter.limsup` / `Filter.liminf` on sets use the complete lattice of sets.
No second copy of these objects is introduced. All types below are independent
of the candidate implementation. No nonemptiness hypothesis is imposed.
-/

open Set
open scoped MeasureTheory

universe u v

namespace Specs.D11.Ch01.SetSystems

/-- The primary interface is exactly the existing measurable-space type. -/
def measurableSpace_type : Type (u + 1) := Type u → Type u

def measurableSpace_value : measurableSpace_type.{u} :=
  fun α => MeasurableSpace α

def algebra_iff : Prop :=
  ∀ {α : Type u} (A : Set (Set α)),
  MeasureTheory.IsSetAlgebra A ↔
    Set.univ ∈ A ∧ (∀ s ∈ A, sᶜ ∈ A) ∧
      (∀ s ∈ A, ∀ t ∈ A, s ∪ t ∈ A)

def sigmaAlgebra_iff : Prop :=
  ∀ {α : Type u} (A : Set (Set α)),
  (∃ m : MeasurableSpace α, ∀ s, MeasurableSet[m] s ↔ s ∈ A) ↔
    MeasureTheory.IsSetAlgebra A ∧
      (∀ E : ℕ → Set α, (∀ n, E n ∈ A) → (⋃ n, E n) ∈ A)

def algebra_empty : Prop :=
  ∀ {α : Type u} {A : Set (Set α)},
  MeasureTheory.IsSetAlgebra A → (∅ : Set α) ∈ A

def algebra_diff : Prop :=
  ∀ {α : Type u} {A : Set (Set α)} {s t : Set α},
  MeasureTheory.IsSetAlgebra A → s ∈ A → t ∈ A → s \ t ∈ A

def algebra_finite_union : Prop :=
  ∀ {α : Type u} {ι : Type v} {A : Set (Set α)} (_hA : MeasureTheory.IsSetAlgebra A)
  (I : Finset ι) (E : ι → Set α),
  (∀ i ∈ I, E i ∈ A) → (⋃ i ∈ I, E i) ∈ A

def algebra_finite_inter : Prop :=
  ∀ {α : Type u} {ι : Type v} {A : Set (Set α)} (_hA : MeasureTheory.IsSetAlgebra A)
  (I : Finset ι) (E : ι → Set α),
  (∀ i ∈ I, E i ∈ A) → (⋂ i ∈ I, E i) ∈ A

def measurableSets_algebra : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α),
  MeasureTheory.IsSetAlgebra {s : Set α | MeasurableSet[m] s}

def measurable_empty : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α), MeasurableSet[m] (∅ : Set α)

def measurable_diff : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α) {s t : Set α},
  MeasurableSet[m] s → MeasurableSet[m] t → MeasurableSet[m] (s \ t)

def measurable_finite_inter : Prop :=
  ∀ {α : Type u} {ι : Type v} (m : MeasurableSpace α) (I : Finset ι) (E : ι → Set α),
  (∀ i ∈ I, MeasurableSet[m] (E i)) → MeasurableSet[m] (⋂ i ∈ I, E i)

def measurable_countable_union : Prop :=
  ∀ {α : Type u} {ι : Type v} [Countable ι] (m : MeasurableSpace α) (E : ι → Set α),
  (∀ i, MeasurableSet[m] (E i)) → MeasurableSet[m] (⋃ i, E i)

def measurable_countable_inter : Prop :=
  ∀ {α : Type u} {ι : Type v} [Countable ι] (m : MeasurableSpace α) (E : ι → Set α),
  (∀ i, MeasurableSet[m] (E i)) → MeasurableSet[m] (⋂ i, E i)

def limsup_formula : Prop :=
  ∀ {α : Type u} (E : ℕ → Set α),
  Filter.limsup E Filter.atTop = ⋂ N : ℕ, ⋃ n ≥ N, E n

def liminf_formula : Prop :=
  ∀ {α : Type u} (E : ℕ → Set α),
  Filter.liminf E Filter.atTop = ⋃ N : ℕ, ⋂ n ≥ N, E n

def measurable_limsup : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α) (E : ℕ → Set α),
  (∀ n, MeasurableSet[m] (E n)) → MeasurableSet[m] (Filter.limsup E Filter.atTop)

def measurable_liminf : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α) (E : ℕ → Set α),
  (∀ n, MeasurableSet[m] (E n)) → MeasurableSet[m] (Filter.liminf E Filter.atTop)

def generated_contains : Prop :=
  ∀ {α : Type u} (C : Set (Set α)),
  C ⊆ {s : Set α | MeasurableSet[MeasurableSpace.generateFrom C] s}

def generated_le_iff : Prop :=
  ∀ {α : Type u} (C : Set (Set α)) (m : MeasurableSpace α),
  MeasurableSpace.generateFrom C ≤ m ↔ C ⊆ {s : Set α | MeasurableSet[m] s}

def generated_eq_sInf : Prop :=
  ∀ {α : Type u} (C : Set (Set α)),
  MeasurableSpace.generateFrom C =
    sInf {m : MeasurableSpace α | C ⊆ {s : Set α | MeasurableSet[m] s}}

def generated_measurable_iff : Prop :=
  ∀ {α : Type u} (C : Set (Set α)) (s : Set α),
  MeasurableSet[MeasurableSpace.generateFrom C] s ↔
    ∀ m : MeasurableSpace α, C ⊆ {t : Set α | MeasurableSet[m] t} → MeasurableSet[m] s

def generated_mono : Prop :=
  ∀ {α : Type u} {C D : Set (Set α)},
  C ⊆ D → MeasurableSpace.generateFrom C ≤ MeasurableSpace.generateFrom D

def generated_idempotent : Prop :=
  ∀ {α : Type u} (C : Set (Set α)),
  MeasurableSpace.generateFrom {s : Set α | MeasurableSet[MeasurableSpace.generateFrom C] s} =
    MeasurableSpace.generateFrom C

def trace_sigma : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α) (E : Set α),
  @Subtype.instMeasurableSpace α (fun x => x ∈ E) m =
    m.comap (Subtype.val : E → α) ∧
  ∀ B : Set E,
    MeasurableSet[@Subtype.instMeasurableSpace α (fun x => x ∈ E) m] B ↔
      ∃ A : Set α, MeasurableSet[m] A ∧ (Subtype.val : E → α) ⁻¹' A = B

def trace_image_iff : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α) (E : Set α) (B : Set E),
  MeasurableSet[@Subtype.instMeasurableSpace α (fun x => x ∈ E) m] B ↔
    ∃ A : Set α, MeasurableSet[m] A ∧ (Subtype.val : E → α) '' B = E ∩ A

def trace_measurable_iff : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α) {E : Set α},
  MeasurableSet[m] E → ∀ B : Set E,
    MeasurableSet[@Subtype.instMeasurableSpace α (fun x => x ∈ E) m] B ↔
      MeasurableSet[m] ((Subtype.val : E → α) '' B)

def trace_family : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α) {E : Set α}, MeasurableSet[m] E →
  {B : Set α | ∃ A : Set α, MeasurableSet[m] A ∧ B = E ∩ A} =
    {B : Set α | MeasurableSet[m] B ∧ B ⊆ E}

end Specs.D11.Ch01.SetSystems
