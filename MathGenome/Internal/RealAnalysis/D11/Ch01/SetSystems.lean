import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.SetSystems

/-! # Set systems, generation, and trace sigma-algebras

This module uses the native objects listed in the independent Specs.
The first two equivalences check the source axioms against those objects;
subsequent theorems supply the elementary closures, generation properties,
and trace identification. All spaces, including empty spaces, are allowed.
-/

open Set
open scoped MeasureTheory

universe u v

namespace D11.Ch01.SetSystems

/-- The paper's measurable-space structure, definitionally the native type.
This is an abbreviation, so all native instances and results apply unchanged. -/
abbrev measurableSpace (α : Type u) : Type u := MeasurableSpace α

theorem algebra_iff :
  ∀ {α : Type u} (A : Set (Set α)),
  MeasureTheory.IsSetAlgebra A ↔
    Set.univ ∈ A ∧ (∀ s ∈ A, sᶜ ∈ A) ∧
      (∀ s ∈ A, ∀ t ∈ A, s ∪ t ∈ A) := by
  intro α A
  constructor
  · intro h
    exact ⟨h.univ_mem, fun _ hs => h.compl_mem hs, fun _ hs _ ht => h.union_mem hs ht⟩
  · rintro ⟨hU, hc, hu⟩
    exact ⟨by simpa using hc Set.univ hU, fun _ hs => hc _ hs,
      fun _ _ hs ht => hu _ hs _ ht⟩

theorem sigmaAlgebra_iff :
  ∀ {α : Type u} (A : Set (Set α)),
  (∃ m : MeasurableSpace α, ∀ s, MeasurableSet[m] s ↔ s ∈ A) ↔
    MeasureTheory.IsSetAlgebra A ∧
      (∀ E : ℕ → Set α, (∀ n, E n ∈ A) → (⋃ n, E n) ∈ A) := by
  intro α A
  constructor
  · rintro ⟨m, hm⟩
    let : MeasurableSpace α := m
    refine ⟨⟨(hm ∅).mp MeasurableSet.empty, ?_, ?_⟩, ?_⟩
    · intro s hs
      exact (hm sᶜ).mp ((hm s).mpr hs).compl
    · intro s t hs ht
      exact (hm (s ∪ t)).mp (((hm s).mpr hs).union ((hm t).mpr ht))
    · intro E hE
      exact (hm (⋃ n, E n)).mp (MeasurableSet.iUnion fun n => (hm (E n)).mpr (hE n))
  · rintro ⟨hA, hcount⟩
    exact ⟨{
      MeasurableSet' := fun s => s ∈ A
      measurableSet_empty := hA.empty_mem
      measurableSet_compl := fun _ hs => hA.compl_mem hs
      measurableSet_iUnion := hcount
    }, fun _ => Iff.rfl⟩

theorem algebra_empty :
  ∀ {α : Type u} {A : Set (Set α)},
  MeasureTheory.IsSetAlgebra A → (∅ : Set α) ∈ A := by
  intro α A hA
  exact hA.empty_mem

theorem algebra_diff :
  ∀ {α : Type u} {A : Set (Set α)} {s t : Set α},
  MeasureTheory.IsSetAlgebra A → s ∈ A → t ∈ A → s \ t ∈ A := by
  intro α A s t hA hs ht
  exact hA.sdiff_mem hs ht

theorem algebra_finite_union :
  ∀ {α : Type u} {ι : Type v} {A : Set (Set α)} (_hA : MeasureTheory.IsSetAlgebra A)
  (I : Finset ι) (E : ι → Set α),
  (∀ i ∈ I, E i ∈ A) → (⋃ i ∈ I, E i) ∈ A := by
  intro α ι A hA I E hE
  exact hA.biUnion_mem I hE

theorem algebra_finite_inter :
  ∀ {α : Type u} {ι : Type v} {A : Set (Set α)} (_hA : MeasureTheory.IsSetAlgebra A)
  (I : Finset ι) (E : ι → Set α),
  (∀ i ∈ I, E i ∈ A) → (⋂ i ∈ I, E i) ∈ A := by
  intro α ι A hA I E hE
  exact hA.biInter_mem I hE

theorem measurableSets_algebra :
  ∀ {α : Type u} (m : MeasurableSpace α),
  MeasureTheory.IsSetAlgebra {s : Set α | MeasurableSet[m] s} := by
  intro α m
  let : MeasurableSpace α := m
  exact ⟨MeasurableSet.empty, fun _ hs => hs.compl, fun _ _ hs ht => hs.union ht⟩

theorem measurable_empty :
  ∀ {α : Type u} (m : MeasurableSpace α), MeasurableSet[m] (∅ : Set α) := by
  intro α m
  exact @MeasurableSet.empty α m

theorem measurable_diff :
  ∀ {α : Type u} (m : MeasurableSpace α) {s t : Set α},
  MeasurableSet[m] s → MeasurableSet[m] t → MeasurableSet[m] (s \ t) := by
  intro α m s t hs ht
  exact hs.diff ht

theorem measurable_finite_inter :
  ∀ {α : Type u} {ι : Type v} (m : MeasurableSpace α) (I : Finset ι) (E : ι → Set α),
  (∀ i ∈ I, MeasurableSet[m] (E i)) → MeasurableSet[m] (⋂ i ∈ I, E i) := by
  intro α ι m I E hE
  exact I.measurableSet_biInter hE

theorem measurable_countable_union :
  ∀ {α : Type u} {ι : Type v} [Countable ι] (m : MeasurableSpace α) (E : ι → Set α),
  (∀ i, MeasurableSet[m] (E i)) → MeasurableSet[m] (⋃ i, E i) := by
  intro α ι hι m E hE
  exact MeasurableSet.iUnion hE

theorem measurable_countable_inter :
  ∀ {α : Type u} {ι : Type v} [Countable ι] (m : MeasurableSpace α) (E : ι → Set α),
  (∀ i, MeasurableSet[m] (E i)) → MeasurableSet[m] (⋂ i, E i) := by
  intro α ι hι m E hE
  exact MeasurableSet.iInter hE

theorem limsup_formula :
  ∀ {α : Type u} (E : ℕ → Set α),
  Filter.limsup E Filter.atTop = ⋂ N : ℕ, ⋃ n ≥ N, E n := by
  intro α E
  exact Filter.limsup_eq_iInf_iSup_of_nat

theorem liminf_formula :
  ∀ {α : Type u} (E : ℕ → Set α),
  Filter.liminf E Filter.atTop = ⋃ N : ℕ, ⋂ n ≥ N, E n := by
  intro α E
  exact Filter.liminf_eq_iSup_iInf_of_nat

theorem measurable_limsup :
  ∀ {α : Type u} (m : MeasurableSpace α) (E : ℕ → Set α),
  (∀ n, MeasurableSet[m] (E n)) → MeasurableSet[m] (Filter.limsup E Filter.atTop) := by
  intro α m E hE
  rw [limsup_formula]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => hE n

theorem measurable_liminf :
  ∀ {α : Type u} (m : MeasurableSpace α) (E : ℕ → Set α),
  (∀ n, MeasurableSet[m] (E n)) → MeasurableSet[m] (Filter.liminf E Filter.atTop) := by
  intro α m E hE
  rw [liminf_formula]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => hE n

theorem generated_contains :
  ∀ {α : Type u} (C : Set (Set α)),
  C ⊆ {s : Set α | MeasurableSet[MeasurableSpace.generateFrom C] s} := by
  intro α C s hs
  exact MeasurableSpace.measurableSet_generateFrom hs

theorem generated_le_iff :
  ∀ {α : Type u} (C : Set (Set α)) (m : MeasurableSpace α),
  MeasurableSpace.generateFrom C ≤ m ↔ C ⊆ {s : Set α | MeasurableSet[m] s} := by
  intro α C m
  exact MeasurableSpace.generateFrom_le_iff m

theorem generated_eq_sInf :
  ∀ {α : Type u} (C : Set (Set α)),
  MeasurableSpace.generateFrom C =
    sInf {m : MeasurableSpace α | C ⊆ {s : Set α | MeasurableSet[m] s}} := by
  intro α C
  apply le_antisymm
  · exact le_sInf fun m hm => (generated_le_iff C m).mpr hm
  · apply sInf_le
    exact generated_contains C

theorem generated_measurable_iff :
  ∀ {α : Type u} (C : Set (Set α)) (s : Set α),
  MeasurableSet[MeasurableSpace.generateFrom C] s ↔
    ∀ m : MeasurableSpace α, C ⊆ {t : Set α | MeasurableSet[m] t} → MeasurableSet[m] s := by
  intro α C s
  rw [generated_eq_sInf, MeasurableSpace.measurableSet_sInf]
  rfl

theorem generated_mono :
  ∀ {α : Type u} {C D : Set (Set α)},
  C ⊆ D → MeasurableSpace.generateFrom C ≤ MeasurableSpace.generateFrom D := by
  intro α C D h
  exact MeasurableSpace.generateFrom_mono h

theorem generated_idempotent :
  ∀ {α : Type u} (C : Set (Set α)),
  MeasurableSpace.generateFrom {s : Set α | MeasurableSet[MeasurableSpace.generateFrom C] s} =
    MeasurableSpace.generateFrom C := by
  intro α C
  exact @MeasurableSpace.generateFrom_measurableSet α (MeasurableSpace.generateFrom C)

theorem trace_sigma :
  ∀ {α : Type u} (m : MeasurableSpace α) (E : Set α),
  @Subtype.instMeasurableSpace α (fun x => x ∈ E) m =
    m.comap (Subtype.val : E → α) ∧
  ∀ B : Set E,
    MeasurableSet[@Subtype.instMeasurableSpace α (fun x => x ∈ E) m] B ↔
      ∃ A : Set α, MeasurableSet[m] A ∧ (Subtype.val : E → α) ⁻¹' A = B := by
  intro α m E
  exact ⟨rfl, fun _ => Iff.rfl⟩

theorem trace_image_iff :
  ∀ {α : Type u} (m : MeasurableSpace α) (E : Set α) (B : Set E),
  MeasurableSet[@Subtype.instMeasurableSpace α (fun x => x ∈ E) m] B ↔
    ∃ A : Set α, MeasurableSet[m] A ∧ (Subtype.val : E → α) '' B = E ∩ A := by
  intro α m E B
  let : MeasurableSpace α := m
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, Subtype.image_preimage_coe E A⟩
  · rintro ⟨A, hA, hB⟩
    refine ⟨A, hA, ?_⟩
    rw [← Set.preimage_image_eq B Subtype.val_injective, hB]
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

theorem trace_measurable_iff :
  ∀ {α : Type u} (m : MeasurableSpace α) {E : Set α},
  MeasurableSet[m] E → ∀ B : Set E,
    MeasurableSet[@Subtype.instMeasurableSpace α (fun x => x ∈ E) m] B ↔
      MeasurableSet[m] ((Subtype.val : E → α) '' B) := by
  intro α m E hE B
  let : MeasurableSpace α := m
  exact ⟨fun hB => hE.subtype_image hB, fun hB => hB.of_subtype_image⟩

theorem trace_family :
  ∀ {α : Type u} (m : MeasurableSpace α) {E : Set α}, MeasurableSet[m] E →
  {B : Set α | ∃ A : Set α, MeasurableSet[m] A ∧ B = E ∩ A} =
    {B : Set α | MeasurableSet[m] B ∧ B ⊆ E} := by
  intro α m E hE
  let : MeasurableSpace α := m
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨hE.inter hA, Set.inter_subset_left⟩
  · rintro ⟨hB, hBE⟩
    exact ⟨B, hB, (Set.inter_eq_right.mpr hBE).symm⟩

end D11.Ch01.SetSystems
