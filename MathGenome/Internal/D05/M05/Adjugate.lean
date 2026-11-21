import MathGenome.Internal.Specs.D05.M05.Adjugate
import MathGenome.Internal.D05.M05.Cofactor

/-! The adjugate identities of K05.05.adjugate over commutative rings. -/

noncomputable section

namespace D05.M05.Adjugate

def adjugate : D05.Specs.Adjugate.adjugate_type :=
  D05.Specs.Adjugate.adjugate_value

theorem cofactor_entry : D05.Specs.Adjugate.cofactor_entry := by
  intro R _ n A i j
  rfl

theorem matrix_adjugate_bridge : D05.Specs.Adjugate.matrix_adjugate_bridge := by
  intro R _ n A
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    apply Matrix.ext
    intro i j
    rw [cofactor_entry, Matrix.adjugate_fin_succ_eq_det_submatrix]
    unfold D05.M05.cofactor D05.M05.deletedMatrix
    rw [DetDefinition.matrix_det_bridge]

theorem mul_adjugate : D05.Specs.Adjugate.mul_adjugate := by
  intro R _ n A
  rw [matrix_adjugate_bridge, DetDefinition.matrix_det_bridge]
  exact Matrix.mul_adjugate A

theorem adjugate_mul : D05.Specs.Adjugate.adjugate_mul := by
  intro R _ n A
  rw [matrix_adjugate_bridge, DetDefinition.matrix_det_bridge]
  exact Matrix.adjugate_mul A

theorem adjugate_identities : D05.Specs.Adjugate.adjugate_identities := by
  intro R _ n A
  exact ⟨mul_adjugate A, adjugate_mul A⟩

theorem singleton_adjugate : D05.Specs.Adjugate.singleton_adjugate := by
  intro R _ A
  rw [matrix_adjugate_bridge]
  exact Matrix.adjugate_fin_one A

theorem empty_adjugate : D05.Specs.Adjugate.empty_adjugate := by
  intro R _ A B
  exact Subsingleton.elim _ _

theorem empty_identities : D05.Specs.Adjugate.empty_identities := by
  intro R _ A
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end D05.M05.Adjugate
