import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.TotalUnimodularity

/-! Total unimodularity and the closure operations used for equality and bound rows. -/

namespace P205.Polyhedra.TotalUnimodularity

/-- A transparent alias of Mathlib's canonical predicate, with no additional hypotheses. -/
abbrev totalUnimodularity {m n : Type*} (A : Matrix m n ℤ) : Prop :=
  Matrix.IsTotallyUnimodular A

private lemma sign_range_iff (z : ℤ) :
    z ∈ Set.range (SignType.cast : SignType → ℤ) ↔ z = 0 ∨ z = 1 ∨ z = -1 := by
  simp only [SignType.range_eq, SignType.cast, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact or_congr Iff.rfl or_comm

/-- Definition 7.3, using the canonical predicate. -/
theorem square_minors_iff : Specs.P205.Polyhedra.TotalUnimodularity.square_minors_iff := by
  intro m n A
  unfold Matrix.IsTotallyUnimodular
  simp only [sign_range_iff]

/-- Repeated selected rows or columns add only zero determinants. -/
theorem all_minors_iff : Specs.P205.Polyhedra.TotalUnimodularity.all_minors_iff := by
  intro m n A
  rw [Matrix.isTotallyUnimodular_iff]
  simp only [sign_range_iff]

theorem empty_minor : Specs.P205.Polyhedra.TotalUnimodularity.empty_minor := by
  intro m n A f g
  exact Matrix.det_fin_zero

theorem transpose_iff : Specs.P205.Polyhedra.TotalUnimodularity.transpose_iff := by
  intro m n A
  exact Matrix.transpose_isTotallyUnimodular_iff A

theorem submatrix : Specs.P205.Polyhedra.TotalUnimodularity.submatrix := by
  intro m n m' n' A hA f g
  exact hA.submatrix f g

theorem repeat_rows : Specs.P205.Polyhedra.TotalUnimodularity.repeat_rows := by
  intro m n r A hA f
  exact hA.submatrix f id

theorem reindex_iff : Specs.P205.Polyhedra.TotalUnimodularity.reindex_iff := by
  intro m n m' n' A em en
  exact Matrix.reindex_isTotallyUnimodular A em en

/-- Each minor determinant is multiplied by the product of its selected row signs. -/
theorem row_signs : Specs.P205.Polyhedra.TotalUnimodularity.row_signs := by
  intro m n A hA s hs
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intro k f g
  change (Matrix.of (fun i j => s (f i) * (A.submatrix f g) i j)).det ∈ _
  rw [Matrix.det_mul_column (fun i => s (f i)) (A.submatrix f g)]
  change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
  apply mul_mem
  · apply prod_mem
    intro i _
    rcases hs (f i) with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  · exact hA k f g

theorem append_unitlike : Specs.P205.Polyhedra.TotalUnimodularity.append_unitlike := by
  intro m n r _ A B hA hB
  exact hA.fromRows_unitlike hB

theorem append_signed_coordinate_rows :
    Specs.P205.Polyhedra.TotalUnimodularity.append_signed_coordinate_rows := by
  intro m n r _ A hA c s hs
  apply hA.fromRows_unitlike
  intro _ i
  rcases hs i with h | h
  · exact ⟨c i, 1, by simp [h]⟩
  · exact ⟨c i, -1, by simp [h]⟩

/-- First repeat the original rows, then negate the second copy. -/
theorem opposing_rows : Specs.P205.Polyhedra.TotalUnimodularity.opposing_rows := by
  intro m n A hA
  have h := hA.submatrix (Sum.elim id id) id
  have hs : ∀ i : m ⊕ m,
      (Sum.elim (fun _ => (1 : ℤ)) (fun _ => -1)) i = 1 ∨
      (Sum.elim (fun _ => (1 : ℤ)) (fun _ => -1)) i = -1 := by
    rintro (i | i) <;> simp
  have h' := row_signs h (Sum.elim (fun _ => (1 : ℤ)) (fun _ => -1)) hs
  have heq : Matrix.of (fun i j =>
      (Sum.elim (fun _ => (1 : ℤ)) (fun _ => -1)) i *
        A.submatrix (Sum.elim id id) id i j) = Matrix.fromRows A (-A) := by
    ext (i | i) j <;> simp
  rw [heq] at h'
  exact h'

theorem append_bounds : Specs.P205.Polyhedra.TotalUnimodularity.append_bounds := by
  intro m n _ A hA
  apply hA.fromRows_one.fromRows_unitlike
  intro _ i
  refine ⟨i, -1, ?_⟩
  ext j
  by_cases hij : i = j <;> simp [Pi.single_apply, eq_comm, hij]

theorem opposing_rows_with_bounds :
    Specs.P205.Polyhedra.TotalUnimodularity.opposing_rows_with_bounds := by
  intro m n _ A hA
  exact append_bounds (opposing_rows hA)

end P205.Polyhedra.TotalUnimodularity
