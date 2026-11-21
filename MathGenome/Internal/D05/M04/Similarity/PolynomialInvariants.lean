import MathGenome.Internal.Specs.D05.M04.Similarity.PolynomialInvariants
import MathGenome.Internal.D05.M04.Similarity
import MathGenome.Internal.D05.M05.DetProduct
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M08.Minpoly

/-! Polynomial invariants under similarity, K05.04.similarity.
The characteristic-polynomial proof explicitly uses the independently proved
multiplicativity of the shared determinant over the polynomial ring.
-/

noncomputable section

namespace D05.M04.Similarity.PolynomialInvariants

/-- Polynomial covariance implies equality of the sets of annihilators. -/
theorem annihilates_iff : Specs.D05.M04.Similarity.PolynomialInvariants.annihilates_iff := by
  exact D05.M04.Similarity.annihilates_iff

theorem minimalPolynomial_matrix_bridge : Specs.D05.M04.Similarity.PolynomialInvariants.minimalPolynomial_matrix_bridge := by
  intro K _ n A
  exact (minpoly.algEquiv_eq
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] _) A).symm

/-- Each monic minimal polynomial divides the other, since they have the
same annihilators. No positive-size or splitting assumption is used. -/
theorem minpoly_invariant : Specs.D05.M04.Similarity.PolynomialInvariants.minpoly_invariant := by
  intro K _ n A B h
  have hm (M : Matrix (Fin n) (Fin n) K) : (minpoly K M).Monic := by
    rw [minimalPolynomial_matrix_bridge M]
    exact D05.M08.Minpoly.monic (Matrix.toLin' M)
  apply Polynomial.eq_of_monic_of_associated (hm B) (hm A)
  apply associated_of_dvd_dvd
  · apply minpoly.dvd K B
    exact (annihilates_iff A B h (minpoly K A)).mpr (minpoly.aeval K A)
  · apply minpoly.dvd K A
    exact (annihilates_iff A B h (minpoly K B)).mp (minpoly.aeval K B)

theorem minimalPolynomial_invariant : Specs.D05.M04.Similarity.PolynomialInvariants.minimalPolynomial_invariant := by
  intro K _ n A B h
  rw [← minimalPolynomial_matrix_bridge B, ← minimalPolynomial_matrix_bridge A]
  exact minpoly_invariant A B h

theorem charmatrix_conjugation : Specs.D05.M04.Similarity.PolynomialInvariants.charmatrix_conjugation := by
  exact D05.M04.Similarity.charmatrix_conjugation

/-- Apply determinant multiplicativity in R[t]. The determinants of the
constant change matrices multiply to one, including for empty matrices. -/
theorem determinant_invariant : Specs.D05.M04.Similarity.PolynomialInvariants.determinant_invariant := by
  intro R _ n A B h
  obtain ⟨P, hP, rfl⟩ := h
  rw [charmatrix_conjugation A P hP, D05.M05.DetProduct.det_mul,
    D05.M05.DetProduct.det_mul]
  have hinv : P⁻¹.map Polynomial.C * P.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul]
    obtain ⟨u, rfl⟩ := hP
    simp [← Matrix.coe_units_inv]
  have hdet : D05.M05.determinant (P⁻¹.map Polynomial.C) *
      D05.M05.determinant (P.map Polynomial.C) = 1 := by
    rw [← D05.M05.DetProduct.det_mul, hinv]
    exact D05.M05.DetDefinition.identity_determinant n
  calc
    _ = (D05.M05.determinant (P⁻¹.map Polynomial.C) *
          D05.M05.determinant (P.map Polynomial.C)) *
          D05.M05.determinant
            (Matrix.scalar (Fin n) (Polynomial.X : Polynomial R) - A.map Polynomial.C) := by
      ac_rfl
    _ = _ := by rw [hdet, one_mul]

/-- The shared determinant bridge identifies the preceding equality with
Mathlib's characteristic polynomial, just as in K05.08.charpoly. -/
theorem charpoly_invariant : Specs.D05.M04.Similarity.PolynomialInvariants.charpoly_invariant := by
  intro R _ n A B h
  have hd := determinant_invariant A B h
  rw [D05.M05.DetDefinition.matrix_det_bridge,
    D05.M05.DetDefinition.matrix_det_bridge] at hd
  exact hd

end D05.M04.Similarity.PolynomialInvariants
