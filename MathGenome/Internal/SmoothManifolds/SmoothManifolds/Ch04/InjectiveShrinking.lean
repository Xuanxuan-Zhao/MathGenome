import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.InjectiveShrinking

namespace SmoothManifolds
open Set Topology
universe u v

/-- Closed-image form of shrinking, valid for any regular paracompact target. -/
theorem injective_shrinking_of_isClosed_image
    {U : Type u} {N : Type v} [TopologicalSpace U] [TopologicalSpace N]
    [RegularSpace N] [ParacompactSpace N]
    (F : U → N) (S : Set U) (hF : Continuous F)
    (hE : IsEmbedding (fun s : S => F s)) (hC : IsClosed (F '' S))
    (hlocal : ∀ s ∈ S, ∃ W : Set U, IsOpen W ∧ s ∈ W ∧ InjOn F W) :
    ∃ V : Set U, IsOpen V ∧ S ⊆ V ∧ InjOn F V := by
  classical
  have hcover : ∀ y : N, ∃ (A : Set U) (B : Set N),
      IsOpen A ∧ InjOn F A ∧ IsOpen B ∧ y ∈ B ∧
        ∀ s ∈ S, F s ∈ B → s ∈ A := by
    intro y
    by_cases hy : y ∈ F '' S
    · obtain ⟨s, hs, rfl⟩ := hy
      obtain ⟨A, hAo, hsA, hAi⟩ := hlocal s hs
      obtain ⟨B, hBo, hB⟩ := hE.isInducing.isOpen_iff.mp
        (hAo.preimage (continuous_subtype_val : Continuous (Subtype.val : S → U)))
      refine ⟨A, B, hAo, hAi, hBo, ?_, ?_⟩
      · have : (⟨s, hs⟩ : S) ∈ (fun s : S => F s) ⁻¹' B := by
          rw [hB]
          exact hsA
        exact this
      · intro t ht hFt
        have : (⟨t, ht⟩ : S) ∈ (fun s : S => F s) ⁻¹' B := hFt
        rw [hB] at this
        exact this
    · refine ⟨∅, (F '' S)ᶜ, isOpen_empty, ?_, hC.isOpen_compl, hy, ?_⟩
      · intro x hx
        exact hx.elim
      · intro s hs hFs
        exact (hFs ⟨s, hs, rfl⟩).elim
  choose A B hAo hAi hBo hyB hBA using hcover
  have hsmall : ∀ y : N, ∃ C : Set N, IsOpen C ∧ y ∈ C ∧ closure C ⊆ B y := by
    intro y
    obtain ⟨C, ⟨hy, hCo⟩, hCB⟩ :=
      (nhds_basis_opens y).nhds_closure.mem_iff.mp ((hBo y).mem_nhds (hyB y))
    exact ⟨C, hCo, hy, hCB⟩
  choose C hCo hyC hCB using hsmall
  obtain ⟨W, hWo, hWcov, hWfin, hWC⟩ := precise_refinement C hCo
    (iUnion_eq_univ_iff.mpr fun y => ⟨y, hyC y⟩)
  let bad : N → Set U := fun y => F ⁻¹' closure (W y) \ A y
  have hbad : IsClosed (⋃ y, bad y) := by
    apply ((hWfin.closure.preimage_continuous hF).subset
      (fun y => (sdiff_subset : bad y ⊆ F ⁻¹' closure (W y)))).isClosed_iUnion
    intro y
    exact (isClosed_closure.preimage hF).sdiff (hAo y)
  refine ⟨(⋃ y, bad y)ᶜ, hbad.isOpen_compl, ?_, ?_⟩
  · intro s hs hbadS
    obtain ⟨y, hsy⟩ := mem_iUnion.mp hbadS
    exact hsy.2 (hBA y s hs (hCB y (closure_mono (hWC y) hsy.1)))
  · intro x hx z hz hxz
    obtain ⟨y, hy⟩ := iUnion_eq_univ_iff.mp hWcov (F x)
    have hxA : x ∈ A y := by
      by_contra h
      exact hx (mem_iUnion.mpr ⟨y, subset_closure hy, h⟩)
    have hzA : z ∈ A y := by
      by_contra h
      exact hz (mem_iUnion.mpr ⟨y, subset_closure (hxz ▸ hy), h⟩)
    exact hAi y hxA hzA hxz

/-- Shrinking around an embedded locally closed image (paper, Chapter 4). -/
theorem injective_shrinking
    {U : Type u} {N : Type v} [TopologicalSpace U] [TopologicalSpace N]
    {n : ℕ} {kind : ModelKind} (A : TopologicalManifold n kind N)
    (F : U → N) (S : Set U) (hF : Continuous F)
    (hE : IsEmbedding (fun s : S => F s)) (hC : IsLocallyClosed (F '' S))
    (hlocal : ∀ s ∈ S, ∃ W : Set U, IsOpen W ∧ s ∈ W ∧ InjOn F W) :
    ∃ V : Set U, IsOpen V ∧ S ⊆ V ∧ InjOn F V := by
  let : RegularSpace N := A.regularSpace
  let : SecondCountableTopology N := A.secondCountable
  obtain ⟨O, C, hOo, hCc, hEq⟩ := hC
  have hSO : ∀ s ∈ S, F s ∈ O := by
    intro s hs
    have h : F s ∈ F '' S := ⟨s, hs, rfl⟩
    rw [hEq] at h
    exact h.1
  let T : Set U := F ⁻¹' O
  let S' : Set T := Subtype.val ⁻¹' S
  let f : T → O := fun x => ⟨F x, x.property⟩
  have hf : Continuous f := (hF.comp continuous_subtype_val).subtype_mk _
  have hj : IsEmbedding (fun s : S' => (⟨s.val.val, s.property⟩ : S)) := by
    have hh : IsEmbedding (fun s : S' => (s.val.val : U)) :=
      (show IsEmbedding (Subtype.val : T → U) from .subtypeVal).comp
        (show IsEmbedding (Subtype.val : S' → T) from .subtypeVal)
    exact (show IsEmbedding (Subtype.val : S → U) from .subtypeVal).of_comp_iff.mp hh
  have he : IsEmbedding (fun s : S' => f s) :=
    (hE.comp hj).codRestrict O (fun s => s.val.property)
  have hc : IsClosed (f '' S') := by
    have him : f '' S' = (Subtype.val : O → N) ⁻¹' C := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h : F x.val ∈ F '' S := ⟨x.val, hx, rfl⟩
        rw [hEq] at h
        exact h.2
      · intro hy
        have h : y.val ∈ F '' S := by
          rw [hEq]
          exact ⟨y.property, hy⟩
        obtain ⟨x, hx, hxy⟩ := h
        have hxO : F x ∈ O := hxy.symm ▸ y.property
        exact ⟨⟨x, hxO⟩, hx, Subtype.ext hxy⟩
    rw [him]
    exact hCc.preimage continuous_subtype_val
  have hl : ∀ s ∈ S', ∃ W : Set T, IsOpen W ∧ s ∈ W ∧ InjOn f W := by
    intro s hs
    obtain ⟨W, hWo, hsW, hWi⟩ := hlocal s.val hs
    refine ⟨Subtype.val ⁻¹' W, hWo.preimage continuous_subtype_val, hsW, ?_⟩
    intro x hx y hy hxy
    apply Subtype.ext
    exact hWi hx hy (congrArg Subtype.val hxy)
  let : ParacompactSpace O :=
    D10Topology.Ch15.regular_lindelof_paracompact O inferInstance inferInstance
  obtain ⟨V, hVo, hSV, hVi⟩ := injective_shrinking_of_isClosed_image f S' hf he hc hl
  refine ⟨Subtype.val '' V, (hOo.preimage hF).isOpenMap_subtype_val V hVo, ?_, ?_⟩
  · intro s hs
    exact ⟨⟨s, hSO s hs⟩, hSV hs, rfl⟩
  · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ hab
    exact congrArg Subtype.val (hVi ha hb (Subtype.ext hab))

end SmoothManifolds
