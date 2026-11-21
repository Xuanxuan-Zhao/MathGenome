import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.FieldRecovery
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
Independent statements for FT-C04, notes/003/advanced-field-theory.tex:708–740.
The extension is algebraic Galois; the topology is the canonical Krull topology.
The subgroup in the closure identities is arbitrary, with no closedness assumption.
`Subgroup.topologicalClosure` has carrier equal to the topological closure of
its original carrier, and supplies the subgroup structure on that closure.
-/

universe u v
noncomputable section

namespace Specs.AdvancedFieldTheory

/-- The pointwise stabilizer of the fixed field is precisely the closure. -/
def fixingSubgroup_fixedField_eq_topologicalClosure_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)),
    (IntermediateField.fixedField H).fixingSubgroup = H.topologicalClosure

/-- Passing to the closure does not change the fixed field. -/
def fixedField_topologicalClosure_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)),
    IntermediateField.fixedField H.topologicalClosure = IntermediateField.fixedField H

/-- The correspondence is an order isomorphism with the order dual of the
closed subgroups. Both directions are the canonical fixing/fixed assignments. -/
def infiniteGaloisCorrespondence_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    ∃ e : IntermediateField K L ≃o (ClosedSubgroup (L ≃ₐ[K] L))ᵒᵈ,
      (∀ M, (e M).toSubgroup = M.fixingSubgroup) ∧
      (∀ H, e.symm H = IntermediateField.fixedField H.toSubgroup)

end Specs.AdvancedFieldTheory
