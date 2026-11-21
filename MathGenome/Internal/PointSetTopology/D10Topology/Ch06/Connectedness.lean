import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.Connectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Subspaces
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ClosureCalculus

/-!
Source connectedness is absence of a separation, including empty spaces.
The bridge to Mathlib is to preconnectedness. No separation axiom is used.
The subspace separation test uses ambient closures, not disjoint closures.
-/

open Set Topology
universe u v

namespace D10Topology.Ch06

def Separation {X : Type u} [TopologicalSpace X] (U V : Set X) : Prop :=
  ConnectednessData.Separation U V

def Connected (X : Type u) [TopologicalSpace X] : Prop :=
  ConnectednessData.Connected X

def ConnectedSubset {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ConnectednessData.ConnectedSubset A

def Separated {X : Type u} [TopologicalSpace X] (A B : Set X) : Prop :=
  ConnectednessData.Separated A B

section Basic
variable {X : Type u} [TopologicalSpace X]

/-- The pieces of a separation are complementary. -/
theorem separation_complement {U V : Set X} (h : Separation U V) : Uᶜ = V := by
  rcases h with ⟨_, _, _, _, hcov, hdis⟩
  ext x
  constructor
  · intro hx
    have hxUV : x ∈ U ∪ V := hcov.symm ▸ mem_univ x
    exact hxUV.resolve_left hx
  · intro hxV hxU
    have : x ∈ U ∩ V := ⟨hxU, hxV⟩
    rw [hdis] at this
    exact this

/-- Both relatively open pieces are also relatively closed. -/
theorem separation_clopen {U V : Set X} (h : Separation U V) :
    IsClopen U ∧ IsClopen V := by
  have hcomp := separation_complement h
  have hUc : IsOpen Uᶜ := hcomp.symm ▸ h.2.1
  have hVc : IsOpen Vᶜ := by rw [← hcomp, compl_compl]; exact h.1
  exact ⟨⟨isOpen_compl_iff.mp hUc, h.1⟩, ⟨isOpen_compl_iff.mp hVc, h.2.1⟩⟩

end Basic

theorem connected_iff_clopen (X : Type u) [TopologicalSpace X] :
    Connected X ↔ ∀ U : Set X, IsClopen U → U = ∅ ∨ U = univ := by
  constructor
  · intro h U hU
    by_cases he : U = ∅
    · exact Or.inl he
    by_cases hu : U = univ
    · exact Or.inr hu
    exfalso
    apply h
    exact ⟨U, Uᶜ, hU.isOpen, hU.isClosed.isOpen_compl, nonempty_iff_ne_empty.mpr he,
      (ne_univ_iff_exists_notMem U).mp hu, union_compl_self U, inter_compl_self U⟩
  · intro h
    rintro ⟨U, V, hsep⟩
    rcases h U (separation_clopen hsep).1 with he | hu
    · exact hsep.2.2.1.ne_empty he
    · obtain ⟨x, hxV⟩ := hsep.2.2.2.1
      have hxU : x ∈ U := hu.symm ▸ mem_univ x
      have hx : x ∈ U ∩ V := ⟨hxU, hxV⟩
      rw [hsep.2.2.2.2.2] at hx
      exact hx

theorem connected_iff_preconnectedSpace (X : Type u) [TopologicalSpace X] :
    Connected X ↔ PreconnectedSpace X :=
  (connected_iff_clopen X).trans preconnectedSpace_iff_clopen.symm

theorem connectedSubset_iff_isPreconnected {X : Type u} [TopologicalSpace X] (A : Set X) :
    ConnectedSubset A ↔ IsPreconnected A :=
  (connected_iff_preconnectedSpace A).trans isPreconnected_iff_preconnectedSpace.symm

theorem connected_iff_bool_maps (X : Type u) [t : TopologicalSpace X] :
    Connected X ↔ ∀ f : X → Bool, @Continuous X Bool t ⊥ f → ∀ x y, f x = f y := by
  constructor
  · intro h f hf x y
    let : TopologicalSpace Bool := ⊥
    have hcl : IsClopen (f ⁻¹' {f x}) :=
      (show IsClopen ({f x} : Set Bool) from ⟨isOpen_compl_iff.mp trivial, trivial⟩).preimage hf
    rcases (connected_iff_clopen X).mp h _ hcl with he | hu
    · have hx : x ∈ f ⁻¹' {f x} := mem_singleton _
      rw [he] at hx
      exact hx.elim
    · have hy : y ∈ f ⁻¹' {f x} := hu.symm ▸ mem_univ y
      exact (mem_singleton_iff.mp hy).symm
  · intro h
    apply (connected_iff_clopen X).mpr
    intro U hU
    by_cases he : U = ∅
    · exact Or.inl he
    right
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr he
    apply eq_univ_of_forall
    intro y
    by_contra hy
    have hc := h (Ch02.characteristic U)
      ((Ch02.characteristic_discrete_continuous_iff_clopen U).mpr hU) x y
    classical
    simp [Ch02.characteristic, Ch02.CharacteristicMaps.chi, hx, hy] at hc

theorem connected_of_subsingleton (X : Type u) [TopologicalSpace X] [Subsingleton X] :
    Connected X := by
  apply (connected_iff_preconnectedSpace X).mpr
  exact ⟨(show (univ : Set X).Subsingleton from fun _ _ _ _ => Subsingleton.elim _ _).isPreconnected⟩

theorem connectedSubset_empty (X : Type u) [TopologicalSpace X] :
    ConnectedSubset (∅ : Set X) :=
  (connectedSubset_iff_isPreconnected _).mpr isPreconnected_empty

theorem connectedSubset_singleton {X : Type u} [TopologicalSpace X] (x : X) :
    ConnectedSubset ({x} : Set X) :=
  (connectedSubset_iff_isPreconnected _).mpr isPreconnected_singleton


/-- Ambient form of the closure fixed-point test for a relatively closed set. -/
theorem closed_subspace_trace_closure {X : Type u} [TopologicalSpace X]
    (Y A : Set X) (hAY : A ⊆ Y)
    (hA : IsClosed ((Subtype.val : Y → X) ⁻¹' A)) : Y ∩ closure A = A := by
  have heq := Ch03.subspace_closure_ambient Y A hAY
  rw [hA.closure_eq, Ch03.subspace_image_preimage, inter_eq_right.mpr hAY] at heq
  exact heq.symm

theorem subspace_separation_iff {X : Type u} [TopologicalSpace X]
    (Y A B : Set X) (hY : Y = A ∪ B) :
    Separation ((Subtype.val : Y → X) ⁻¹' A) ((Subtype.val : Y → X) ⁻¹' B) ↔
      A.Nonempty ∧ B.Nonempty ∧ Separated A B := by
  have hAY : A ⊆ Y := hY.symm ▸ subset_union_left
  have hBY : B ⊆ Y := hY.symm ▸ subset_union_right
  constructor
  · intro hs
    have hcl := separation_clopen hs
    have htraceA := closed_subspace_trace_closure Y A hAY hcl.1.isClosed
    have htraceB := closed_subspace_trace_closure Y B hBY hcl.2.isClosed
    have hdis : A ∩ B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hm : (⟨x, hAY hx.1⟩ : Y) ∈
          ((Subtype.val : Y → X) ⁻¹' A) ∩ ((Subtype.val : Y → X) ⁻¹' B) := hx
      rw [hs.2.2.2.2.2] at hm
      exact hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨y, hy⟩ := hs.2.2.1
      exact ⟨y.val, hy⟩
    · obtain ⟨y, hy⟩ := hs.2.2.2.1
      exact ⟨y.val, hy⟩
    · apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxB : x ∈ B := by
        rw [← htraceB]
        exact ⟨hAY hx.1, hx.2⟩
      have hm : x ∈ A ∩ B := ⟨hx.1, hxB⟩
      rw [hdis] at hm
      exact hm
    · apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxA : x ∈ A := by
        rw [← htraceA]
        exact ⟨hBY hx.1, hx.2⟩
      have hm : x ∈ A ∩ B := ⟨hxA, hx.1⟩
      rw [hdis] at hm
      exact hm
  · rintro ⟨hnA, hnB, hsep⟩
    have hpreA : (Subtype.val : Y → X) ⁻¹' A =
        ((Subtype.val : Y → X) ⁻¹' closure B)ᶜ := by
      ext y
      change (y.val ∈ A) ↔ (y.val ∉ closure B)
      constructor
      · intro hyA hyB
        have hm : y.val ∈ A ∩ closure B := ⟨hyA, hyB⟩
        rw [hsep.1] at hm
        exact hm
      · intro hyB
        have hy : y.val ∈ A ∪ B := hY ▸ y.property
        exact hy.resolve_right (fun hy => hyB (subset_closure hy))
    have hpreB : (Subtype.val : Y → X) ⁻¹' B =
        ((Subtype.val : Y → X) ⁻¹' closure A)ᶜ := by
      ext y
      change (y.val ∈ B) ↔ (y.val ∉ closure A)
      constructor
      · intro hyB hyA
        have hm : y.val ∈ B ∩ closure A := ⟨hyB, hyA⟩
        rw [hsep.2] at hm
        exact hm
      · intro hyA
        have hy : y.val ∈ A ∪ B := hY ▸ y.property
        exact hy.resolve_left (fun hy => hyA (subset_closure hy))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpreA]
      exact (isClosed_closure.preimage continuous_subtype_val).isOpen_compl
    · rw [hpreB]
      exact (isClosed_closure.preimage continuous_subtype_val).isOpen_compl
    · obtain ⟨a, ha⟩ := hnA
      exact ⟨⟨a, hAY ha⟩, ha⟩
    · obtain ⟨b, hb⟩ := hnB
      exact ⟨⟨b, hBY hb⟩, hb⟩
    · apply eq_univ_of_forall
      intro y
      exact hY ▸ y.property
    · apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hm : y.val ∈ A ∩ closure B := ⟨hy.1, subset_closure hy.2⟩
      rw [hsep.1] at hm
      exact hm

theorem connectedSubset_image {X : Type u} {Z : Type v}
    [TopologicalSpace X] [TopologicalSpace Z] (A : Set X) (f : X → Z)
    (hA : ConnectedSubset A) (hf : ContinuousOn f A) : ConnectedSubset (f '' A) :=
  (connectedSubset_iff_isPreconnected _).mpr
    (((connectedSubset_iff_isPreconnected A).mp hA).image f hf)

theorem connected_range {X : Type u} {Z : Type v}
    [TopologicalSpace X] [TopologicalSpace Z] (f : X → Z)
    (hX : Connected X) (hf : Continuous f) : ConnectedSubset (range f) := by
  have := (connected_iff_preconnectedSpace X).mp hX
  exact (connectedSubset_iff_isPreconnected _).mpr (isPreconnected_range hf)

theorem connected_surjective_image {X : Type u} {Z : Type v}
    [TopologicalSpace X] [TopologicalSpace Z] (f : X → Z)
    (hX : Connected X) (hf : Continuous f) (hs : Function.Surjective f) : Connected Z := by
  apply (connected_iff_preconnectedSpace Z).mpr
  apply preconnectedSpace_iff_univ.mpr
  rw [← hs.range_eq]
  exact (connectedSubset_iff_isPreconnected _).mp (connected_range f hX hf)

theorem connectedSubset_between_closure {X : Type u} [TopologicalSpace X]
    (A B : Set X) (hA : ConnectedSubset A) (hAB : A ⊆ B) (hBA : B ⊆ closure A) :
    ConnectedSubset B :=
  (connectedSubset_iff_isPreconnected B).mpr
    (((connectedSubset_iff_isPreconnected A).mp hA).subset_closure hAB hBA)

theorem connectedSubset_closure {X : Type u} [TopologicalSpace X]
    (A : Set X) (hA : ConnectedSubset A) : ConnectedSubset (closure A) :=
  connectedSubset_between_closure A (closure A) hA subset_closure Subset.rfl

theorem connectedSubset_union_meeting {X : Type u} [TopologicalSpace X] {ι : Type v}
    (C : Set X) (A : ι → Set X) (hnC : C.Nonempty) (hC : ConnectedSubset C)
    (hA : ∀ i, ConnectedSubset (A i)) (hm : ∀ i, (C ∩ A i).Nonempty) :
    ConnectedSubset (C ∪ ⋃ i, A i) := by
  apply (connectedSubset_iff_isPreconnected _).mpr
  have hC' := (connectedSubset_iff_isPreconnected C).mp hC
  have hA' := fun i => (connectedSubset_iff_isPreconnected (A i)).mp (hA i)
  obtain ⟨c, hc⟩ := hnC
  apply isPreconnected_of_forall c
  intro y hy
  rcases hy with hy | hy
  · exact ⟨C, subset_union_left, hc, hy, hC'⟩
  · obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    refine ⟨C ∪ A i, ?_, Or.inl hc, Or.inr hyi, hC'.union' (hm i) (hA' i)⟩
    exact union_subset subset_union_left
      (fun z hz => Or.inr (mem_iUnion.mpr ⟨i, hz⟩))

theorem connectedSubset_iUnion_common_point {X : Type u} [TopologicalSpace X] {ι : Type v}
    (A : ι → Set X) (x : X) (hx : ∀ i, x ∈ A i) (hA : ∀ i, ConnectedSubset (A i)) :
    ConnectedSubset (⋃ i, A i) := by
  apply (connectedSubset_iff_isPreconnected _).mpr
  exact isPreconnected_iUnion ⟨x, mem_iInter.mpr hx⟩
    (fun i => (connectedSubset_iff_isPreconnected _).mp (hA i))

theorem connectedSubset_iUnion_empty {X : Type u} [TopologicalSpace X]
    {ι : Type v} [IsEmpty ι] (A : ι → Set X) : ConnectedSubset (⋃ i, A i) := by
  rw [iUnion_of_empty]
  exact connectedSubset_empty X

end D10Topology.Ch06
