import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.CoveringPaths
import Mathlib.Topology.Homotopy.Lifting

namespace D12Complex.Ch20.CoveringPaths

open Set Topology unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- On an open sheet, openness is detected by the homeomorphic restriction
of the projection. -/
private theorem sheet_open_iff {p : E → B} {U : Set B} {V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (h : V ≃ₜ U)
    (hp : ∀ e : V, (h e : B) = p e) {W : Set B} (hWU : W ⊆ U) :
    IsOpen W ↔ IsOpen (p ⁻¹' W ∩ V) := by
  have hWV : p ⁻¹' W ∩ V ⊆ Set.range (Subtype.val : V → E) := by
    simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using
      (inter_subset_right : p ⁻¹' W ∩ V ⊆ V)
  have hWU' : W ⊆ Set.range (Subtype.val : U → B) := by
    simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using hWU
  rw [hU.isOpenEmbedding_subtypeVal.isOpen_iff_preimage_isOpen hWU',
    hV.isOpenEmbedding_subtypeVal.isOpen_iff_preimage_isOpen hWV,
    ← h.isOpen_preimage]
  have heq : h ⁻¹' (Subtype.val ⁻¹' W) =
      (Subtype.val : V → E) ⁻¹' (p ⁻¹' W ∩ V) := by
    ext e
    simp only [mem_preimage, mem_inter_iff, hp, e.property, and_true]
  rw [heq]

/-- Converts the paper's disjoint open sheets into a discrete-fiber
trivialization. No surjectivity or separation assumption is added. -/
theorem covering_bridge (p : E → B) (hp : IsCovering p) : IsCoveringMap p := by
  classical
  intro b
  obtain ⟨U, hbU, hU, sheets, hOpen, hDisj, hCover, hHomeo⟩ := hp b
  by_cases hb : b ∈ Set.range p
  · obtain ⟨e, he⟩ := hb
    have heU : e ∈ ⋃₀ sheets := by rw [hCover]; simpa only [mem_preimage, he] using hbU
    obtain ⟨V, hVs, heV⟩ := Set.mem_sUnion.mp heU
    let S := {V : Set E // V ∈ sheets}
    let : TopologicalSpace S := ⊥
    have : DiscreteTopology S := ⟨rfl⟩
    have : Nonempty S := ⟨⟨V, hVs⟩⟩
    have : Nonempty E := ⟨e⟩
    choose h hh using hHomeo
    have hInj (i : S) : Set.InjOn p i.val := by
      intro x hx y hy hxy
      have : h i.val i.property ⟨x, hx⟩ = h i.val i.property ⟨y, hy⟩ := by
        apply Subtype.ext
        simpa only [hh] using hxy
      exact congrArg Subtype.val ((h i.val i.property).injective this)
    have hSurj (i : S) : Set.SurjOn p i.val U := by
      intro x hx
      refine ⟨((h i.val i.property).symm ⟨x, hx⟩ : E), Subtype.prop _, ?_⟩
      rw [← hh i.val i.property]
      simp
    have hExhaust : p ⁻¹' U ⊆ ⋃ i : S, i.val := by
      intro x hx
      rw [← hCover] at hx
      obtain ⟨V, hV, hxV⟩ := Set.mem_sUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩
    let t : Bundle.Trivialization S p := hU.trivializationDiscrete
      (fun i : S => i.val) U
      (fun i _ hWU => sheet_open_iff hU (hOpen i.val i.property)
        (h i.val i.property) (hh i.val i.property) hWU)
      hInj hSurj hDisj.subtype hExhaust
    exact (IsEvenlyCovered.of_trivialization (t := t) hbU).to_isEvenlyCovered_preimage
  · have hempty : p ⁻¹' U = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro e heU
      rw [← hCover] at heU
      obtain ⟨V, hVs, heV⟩ := Set.mem_sUnion.mp heU
      obtain ⟨h, hh⟩ := hHomeo V hVs
      apply hb
      refine ⟨(h.symm ⟨b, hbU⟩ : E), ?_⟩
      rw [← hh]
      simp
    exact (IsEvenlyCovered.of_preimage_eq_empty (f := p) Empty
      (hU.mem_nhds hbU) hempty).to_isEvenlyCovered_preimage

/-- Existence and uniqueness of a continuous lift from any chosen point
over the initial endpoint. -/
theorem path_lifting (p : E → B) (hp : IsCovering p)
    (γ : I → B) (hγ : Continuous γ) (e₀ : E) (he₀ : p e₀ = γ 0) :
    ∃! Γ : I → E, Continuous Γ ∧ Γ 0 = e₀ ∧ p ∘ Γ = γ := by
  let cov := covering_bridge p hp
  obtain ⟨Γ, hΓp, hΓ0⟩ := cov.exists_path_lifts ⟨γ, hγ⟩ e₀ he₀.symm
  refine ⟨Γ, ⟨Γ.continuous, hΓ0, hΓp⟩, ?_⟩
  intro Γ' hΓ'
  exact cov.eq_of_comp_eq hΓ'.1 Γ.continuous
    (hΓ'.2.2.trans hΓp.symm) 0 (hΓ'.2.1.trans hΓ0.symm)

end D12Complex.Ch20.CoveringPaths
