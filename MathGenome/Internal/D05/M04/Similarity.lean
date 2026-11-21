import MathGenome.Internal.Specs.D05.M04.Similarity
import MathGenome.Internal.D05.M04.ChangeBasis

/-! Similarity and its polynomial consequences, K05.04.similarity. -/

namespace D05.M04.Similarity

open Matrix

noncomputable def similar : Specs.D05.M04.Similarity.similar_type :=
  Specs.D05.M04.Similarity.similar_value

/-- Conjugation by an invertible matrix is an algebra automorphism.
The direction is the paper's `P⁻¹ A P`. -/
def conjugation {R : Type*} [CommRing R] {n : ℕ}
    (P : (Matrix (Fin n) (Fin n) R)ˣ) :
    Matrix (Fin n) (Fin n) R ≃ₐ[R] Matrix (Fin n) (Fin n) R where
  toFun A := ↑P⁻¹ * A * ↑P
  invFun A := ↑P * A * ↑P⁻¹
  left_inv A := by simp [mul_assoc]
  right_inv A := by simp [mul_assoc]
  map_mul' A B := by simp [mul_assoc]
  map_add' A B := by simp [mul_add, add_mul]
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one]

theorem same_basis_conjugation : Specs.D05.M04.Similarity.same_basis_conjugation := by
  intro R V _ _ _ n b b' T
  exact D05.M04.ChangeBasis.change_basis b b' b b' T

theorem same_basis_similar : Specs.D05.M04.Similarity.same_basis_similar := by
  intro R V _ _ _ n b b' T
  exact ⟨_, D05.M04.ChangeBasis.conversion_isUnit b b', same_basis_conjugation b b' T⟩

theorem reflexive : Specs.D05.M04.Similarity.reflexive := by
  intro R _ n A
  exact ⟨1, isUnit_one, by simp⟩

theorem symmetric : Specs.D05.M04.Similarity.symmetric := by
  intro R _ n A B
  rintro ⟨P, ⟨u, rfl⟩, rfl⟩
  refine ⟨↑u⁻¹, u⁻¹.isUnit, ?_⟩
  simp [← Matrix.coe_units_inv, mul_assoc]

theorem transitive : Specs.D05.M04.Similarity.transitive := by
  intro R _ n A B C
  rintro ⟨P, ⟨u, rfl⟩, rfl⟩ ⟨Q, ⟨v, rfl⟩, rfl⟩
  refine ⟨↑(u * v), (u * v).isUnit, ?_⟩
  simp only [← Matrix.coe_units_inv]
  simp [mul_assoc]

theorem equivalence : Specs.D05.M04.Similarity.equivalence := by
  intro R _ n
  exact ⟨reflexive, fun h => symmetric _ _ h, fun h h' => transitive _ _ _ h h'⟩

theorem power_conjugation : Specs.D05.M04.Similarity.power_conjugation := by
  intro R _ n A P hP k
  obtain ⟨u, rfl⟩ := hP
  have h := (conjugation u).map_pow A k
  change (↑u⁻¹ : Matrix (Fin n) (Fin n) R) * A ^ k *
      (↑u : Matrix (Fin n) (Fin n) R) =
    ((↑u⁻¹ : Matrix (Fin n) (Fin n) R) * A *
      (↑u : Matrix (Fin n) (Fin n) R)) ^ k at h
  simpa only [Matrix.coe_units_inv] using h.symm

theorem polynomial_conjugation : Specs.D05.M04.Similarity.polynomial_conjugation := by
  intro R _ n A P hP p
  obtain ⟨u, rfl⟩ := hP
  simpa only [conjugation, AlgEquiv.coe_mk, Equiv.coe_fn_mk, Matrix.coe_units_inv]
    using Polynomial.aeval_algHom_apply (conjugation u) A p

theorem polynomial_similar : Specs.D05.M04.Similarity.polynomial_similar := by
  intro R _ n A B
  rintro ⟨P, hP, rfl⟩ p
  exact ⟨P, hP, polynomial_conjugation A P hP p⟩

theorem annihilates_iff : Specs.D05.M04.Similarity.annihilates_iff := by
  intro R _ n A B
  rintro ⟨P, ⟨u, rfl⟩, rfl⟩ p
  rw [polynomial_conjugation A (↑u) u.isUnit p]
  rw [← Matrix.coe_units_inv]
  change conjugation u (Polynomial.aeval A p) = 0 ↔ _
  exact (conjugation u).map_eq_zero_iff

theorem minpoly_invariant : Specs.D05.M04.Similarity.minpoly_invariant := by
  intro K _ n A B
  rintro ⟨P, ⟨u, rfl⟩, rfl⟩
  simpa only [conjugation, AlgEquiv.coe_mk, Equiv.coe_fn_mk, Matrix.coe_units_inv]
    using minpoly.algEquiv_eq (conjugation u) A

theorem charmatrix_conjugation : Specs.D05.M04.Similarity.charmatrix_conjugation := by
  intro R _ n A P hP
  obtain ⟨u, rfl⟩ := hP
  have h : A * (↑u : Matrix (Fin n) (Fin n) R) =
      (↑u : Matrix (Fin n) (Fin n) R) *
        ((↑u : Matrix (Fin n) (Fin n) R)⁻¹ * A *
          (↑u : Matrix (Fin n) (Fin n) R)) := by
    simp [← Matrix.coe_units_inv, mul_assoc]
  have hc := Matrix.charmatrix_mul_map_C_of_mul_eq_mul h
  have hi : (↑u : Matrix (Fin n) (Fin n) R)⁻¹.map Polynomial.C *
      (↑u : Matrix (Fin n) (Fin n) R).map Polynomial.C = 1 := by
    rw [← Matrix.map_mul]
    simp [← Matrix.coe_units_inv]
  have hc' := congrArg
    (fun X : Matrix (Fin n) (Fin n) (Polynomial R) =>
      (↑u : Matrix (Fin n) (Fin n) R)⁻¹.map Polynomial.C * X) hc
  simpa only [← mul_assoc, hi, one_mul] using hc'.symm

theorem charpoly_invariant : Specs.D05.M04.Similarity.charpoly_invariant := by
  intro R _ n A B
  rintro ⟨P, ⟨u, rfl⟩, rfl⟩
  exact Matrix.charpoly_units_conj' u A

end D05.M04.Similarity
