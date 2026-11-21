import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Closure.FiniteCoordinates
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.FieldRecovery
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.FiniteLayerFixedField
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.InfiniteGalois

/-! # Closure and the infinite Galois correspondence

FT-C04. The finite-layer restriction image detects the stabilizer of a
fixed field. The finite-coordinate closure criterion then identifies it
with the closure, including for nonclosed subgroups.
-/

universe u v
noncomputable section

namespace AdvancedFieldTheory

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- The subgroup fixing the fixed field of H is the topological closure of H. -/
theorem fixingSubgroup_fixedField_eq_topologicalClosure
    (H : Subgroup (GaloisGroup K L)) :
    fixingSubgroup (fixedField H) = H.topologicalClosure := by
  apply le_antisymm
  · intro σ hσ
    apply (KrullTopology.mem_closure_iff_finiteCoordinates (H : Set (GaloisGroup K L)) σ).mpr
    intro E
    have hmem : restriction E.toIntermediateField σ ∈
        fixingSubgroup ((fixedField H).comap E.toIntermediateField.val) := by
      apply (mem_fixingSubgroup _ _).mpr
      intro x hx
      apply Subtype.ext
      rw [restriction_apply]
      exact (mem_fixingSubgroup (fixedField H) σ).mp hσ x hx
    rw [← restriction_image_eq_fixingSubgroup H E.toIntermediateField] at hmem
    exact Subgroup.mem_map.mp hmem
  · apply H.topologicalClosure_minimal
    · intro σ hσ
      apply (mem_fixingSubgroup (fixedField H) σ).mpr
      intro x hx
      exact (mem_fixedField H x).mp hx σ hσ
    · exact fixingSubgroup_isClosed K L (fixedField H)

/-- The topological closure of an arbitrary subgroup has the same fixed field. -/
theorem fixedField_topologicalClosure (H : Subgroup (GaloisGroup K L)) :
    fixedField H.topologicalClosure = fixedField H := by
  rw [← fixingSubgroup_fixedField_eq_topologicalClosure H]
  exact fixedField_fixingSubgroup K L (fixedField H)

/-- The canonical fixing and fixed assignments yield an inclusion-reversing
bijection between all intermediate fields and all Krull-closed subgroups. -/
theorem infiniteGaloisCorrespondence (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    ∃ e : IntermediateField K L ≃o (ClosedSubgroup (GaloisGroup K L))ᵒᵈ,
      (∀ M, (e M).toSubgroup = fixingSubgroup M) ∧
      (∀ H, e.symm H = fixedField H.toSubgroup) := by
  let e : IntermediateField K L ≃o (ClosedSubgroup (GaloisGroup K L))ᵒᵈ :=
    { toFun := fun M => ⟨fixingSubgroup M, fixingSubgroup_isClosed K L M⟩
      invFun := fun H => fixedField H.toSubgroup
      left_inv := fun M => fixedField_fixingSubgroup K L M
      right_inv := by
        intro H
        apply ClosedSubgroup.toSubgroup_injective
        change fixingSubgroup (fixedField H.toSubgroup) = H.toSubgroup
        rw [fixingSubgroup_fixedField_eq_topologicalClosure]
        apply SetLike.ext'
        exact H.isClosed'.closure_eq
      map_rel_iff' := by
        intro M N
        change fixingSubgroup N ≤ fixingSubgroup M ↔ M ≤ N
        constructor
        · intro h
          have hf := IntermediateField.fixedField_le h
          change fixedField (fixingSubgroup M) ≤ fixedField (fixingSubgroup N) at hf
          simpa only [fixedField_fixingSubgroup K L] using hf
        · exact IntermediateField.fixingSubgroup_le }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

end AdvancedFieldTheory
