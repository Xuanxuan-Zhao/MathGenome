import MathGenome.Internal.Specs.D05.M04.MatrixProduct

/-! Matrix arithmetic from K05.04.matrix_product, over commutative rings. -/
namespace D05.M04.MatrixProduct

open scoped BigOperators

theorem add_entry : MatrixProductSpec.add_entry := by
  intro R _ l n _ _ A B i j
  rfl

theorem smul_entry : MatrixProductSpec.smul_entry := by
  intro R _ l n _ _ a A i j
  rfl

theorem mul_entry : MatrixProductSpec.mul_entry := by
  intro R _ l m n _ _ _ A B i j
  exact Matrix.mul_apply

theorem mul_assoc : MatrixProductSpec.mul_assoc := by
  intro R _ l m n p _ _ _ _ A B C
  exact Matrix.mul_assoc A B C

theorem triple_mul_entry : MatrixProductSpec.triple_mul_entry := by
  intro R _ l m n p _ _ _ _ A B C i j
  have expansion : ((A * B) * C) i j =
      ∑ k, ∑ h, (A i h * B h k) * C k j := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
  exact ⟨expansion, (congrArg (fun M : Matrix l p R => M i j)
    (Matrix.mul_assoc A B C)).symm.trans expansion⟩

theorem sum_interchange : MatrixProductSpec.sum_interchange := by
  intro R _ m n _ _ f
  exact Finset.sum_comm

theorem mul_add : MatrixProductSpec.mul_add := by
  intro R _ l m n _ _ _ A B C
  exact Matrix.mul_add A B C

theorem add_mul : MatrixProductSpec.add_mul := by
  intro R _ l m n _ _ _ A B C
  exact Matrix.add_mul A B C

theorem smul_mul : MatrixProductSpec.smul_mul := by
  intro R _ l m n _ _ _ a A B
  exact Matrix.smul_mul a A B

theorem mul_smul : MatrixProductSpec.mul_smul := by
  intro R _ l m n _ _ _ a A B
  exact Matrix.mul_smul A a B

theorem one_entry : MatrixProductSpec.one_entry := by
  intro R _ n _ _ i j
  simp only [Matrix.one_apply]

theorem mul_one : MatrixProductSpec.mul_one := by
  intro R _ l n _ _ _ A
  exact Matrix.mul_one A

theorem one_mul : MatrixProductSpec.one_mul := by
  intro R _ l n _ _ _ A
  exact Matrix.one_mul A

theorem mul_empty : MatrixProductSpec.mul_empty := by
  intro R _ l m n _ _ _ _ A B
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Finset.univ_eq_empty, Finset.sum_empty, Matrix.zero_apply]

end D05.M04.MatrixProduct
