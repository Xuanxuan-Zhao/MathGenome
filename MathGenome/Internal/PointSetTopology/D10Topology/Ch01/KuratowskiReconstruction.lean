import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.KuratowskiReconstruction
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.TopologicalFoundations
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ClosureCalculus

/-!
Reconstruction of a topology from the four closure axioms, following
`paper.tex`, d10:01:kuratowski. The fixed sets satisfy the closed-family
axioms; the upstream closed-family characterization supplies the topology.
The least-closed-superset property then identifies its closure on every set.
-/

open Set
open scoped Topology
universe u

namespace D10Topology.Ch01

theorem kuratowski_reconstruction {X : Type u} (c : Set X → Set X)
    (h_ext : ∀ A : Set X, A ⊆ c A)
    (h_idem : ∀ A : Set X, c (c A) = c A)
    (h_union : ∀ A B : Set X, c (A ∪ B) = c A ∪ c B)
    (h_empty : c ∅ = ∅) :
    ∃! t : TopologicalSpace X, ∀ A : Set X, @closure X t A = c A := by
  have h_mono : Monotone c := by
    intro A B hAB
    have h := h_union A B
    rw [union_eq_right.mpr hAB] at h
    exact union_eq_right.mp h.symm
  have h_fixed : ClosedFamilyAxioms {F : Set X | c F = F} := by
    refine ⟨h_empty, ?_, ?_, ?_⟩
    · exact Subset.antisymm (subset_univ _) (h_ext univ)
    · intro S hS
      apply Subset.antisymm _ (h_ext _)
      intro x hx
      apply mem_sInter.mpr
      intro F hF
      have h_le : c (⋂₀ S) ⊆ c F := h_mono (sInter_subset_of_mem hF)
      rw [hS hF] at h_le
      exact h_le hx
    · intro S hfin hS
      induction S, hfin using Set.Finite.induction_on with
      | empty => simpa using h_empty
      | @insert F S hFS hfin ih =>
        have hF : c F = F := hS (by simp)
        have hS' : S ⊆ {F : Set X | c F = F} := fun G hG => hS (by simp [hG])
        change c (⋃₀ insert F S) = ⋃₀ insert F S
        rw [sUnion_insert, h_union, hF, ih hS']
  obtain ⟨t, ht, _⟩ := (closed_characterization _).mp h_fixed
  have h_closed : ∀ F : Set X, IsClosed[t] F ↔ c F = F := by
    intro F
    change F ∈ closedSets t ↔ _
    rw [ht]
    rfl
  have h_closure : ∀ A : Set X, @closure X t A = c A := by
    let := t
    intro A
    apply Subset.antisymm
    · exact closure_minimal (h_ext A) ((h_closed (c A)).mpr (h_idem A))
    · have h_le : c A ⊆ c (closure A) := h_mono (closure_extensive A)
      rw [(h_closed (closure A)).mp isClosed_closure] at h_le
      exact h_le
  refine ⟨t, h_closure, ?_⟩
  intro s hs
  apply TopologicalSpace.ext_isClosed
  intro F
  rw [@closed_iff_closure_fixed X s F, h_closed F, hs F]

end D10Topology.Ch01
