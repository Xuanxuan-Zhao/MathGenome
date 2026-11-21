import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Transfer.GeometricMatrixSeries
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.MultiplicativeInverse
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Transfer.RationalEntries

/-! The adjugate formula for the rational entries of the formal matrix
resolvent (p204:W17). All inverse identities are identities of formal series. -/

noncomputable section
universe u v

namespace FiniteCombinatorics.Transfer

/-- The polynomial matrix I-zM. -/
def polynomialResolvent {R : Type u} [CommRing R] {ι : Type v}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    Matrix ι ι (Polynomial R) :=
  (1 : Matrix ι ι (Polynomial R)) -
      Matrix.of (fun i j => Polynomial.X * Polynomial.C (M i j))

section Ring

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

theorem resolvent_denominator_constant (M : Matrix ι ι R) :
    (polynomialResolvent M).det.coeff 0 = 1 := by
  have h : (Polynomial.constantCoeff : Polynomial R →+* R).mapMatrix
      (polynomialResolvent M) = 1 := by
    apply Matrix.ext
    intro i j
    change Polynomial.constantCoeff
      ((1 : Matrix ι ι (Polynomial R)) i j - Polynomial.X * Polynomial.C (M i j)) =
        (1 : Matrix ι ι R) i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  change Polynomial.constantCoeff (polynomialResolvent M).det = 1
  rw [RingHom.map_det, h, Matrix.det_one]

/-- Coefficient-preserving inclusion identifies the polynomial resolvent with
its previously defined power-series counterpart. -/
theorem map_polynomialResolvent (M : Matrix ι ι R) :
    (Polynomial.coeToPowerSeries.ringHom : Polynomial R →+* PowerSeries R).mapMatrix
      (polynomialResolvent M) = 1 - zMatrix M := by
  apply Matrix.ext
  intro i j
  change (((1 : Matrix ι ι (Polynomial R)) i j -
    Polynomial.X * Polynomial.C (M i j) : Polynomial R) : PowerSeries R) =
      (1 : Matrix ι ι (PowerSeries R)) i j - PowerSeries.X * PowerSeries.C (M i j)
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sub]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> exact mul_comm _ _

/-- Multiply the adjugate identity by the geometric inverse. -/
theorem determinant_mul_geometric_entry (M : Matrix ι ι R) (i j : ι) :
    ((polynomialResolvent M).det : PowerSeries R) * geometricSeries M i j =
      ((polynomialResolvent M).adjugate i j : PowerSeries R) := by
  let A := 1 - zMatrix M
  have hdet : ((polynomialResolvent M).det : PowerSeries R) = A.det := by
    exact ((Polynomial.coeToPowerSeries.ringHom :
      Polynomial R →+* PowerSeries R).map_det _).trans
        (congrArg Matrix.det (map_polynomialResolvent M))
  have hadj : ((polynomialResolvent M).adjugate i j : PowerSeries R) =
      A.adjugate i j := by
    have h := Polynomial.coeToPowerSeries.ringHom.map_adjugate (polynomialResolvent M)
    rw [map_polynomialResolvent] at h
    exact congrArg (fun B => B i j) h
  have hmatrix : A.det • geometricSeries M = A.adjugate := by
    calc
      A.det • geometricSeries M = (A.adjugate * A) * geometricSeries M := by
        rw [Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
      _ = A.adjugate * (A * geometricSeries M) := mul_assoc _ _ _
      _ = A.adjugate := by rw [resolvent_mul_geometric, mul_one]
  rw [hdet, hadj]
  exact congrArg (fun B => B i j) hmatrix

end Ring

variable {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]

theorem geometric_entry_adjugate (M : Matrix ι ι K) (i j : ι) :
    geometricSeries M i j =
      (((polynomialResolvent M).adjugate i j : Polynomial K) : PowerSeries K) *
        (((polynomialResolvent M).det : Polynomial K) : PowerSeries K)⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by
    rw [Polynomial.constantCoeff_coe, resolvent_denominator_constant]
    exact one_ne_zero)).mpr
  rw [mul_comm]
  exact determinant_mul_geometric_entry M i j

theorem entries_are_rational (M : Matrix ι ι K) (i j : ι) :
    ∃ P Q : Polynomial K, Q.coeff 0 = 1 ∧
      geometricSeries M i j = (P : PowerSeries K) * (Q : PowerSeries K)⁻¹ := by
  exact ⟨(polynomialResolvent M).adjugate i j, (polynomialResolvent M).det,
    resolvent_denominator_constant M, geometric_entry_adjugate M i j⟩

theorem inverse_adjugate_formula (M : Matrix ι ι K) :
    ∃ U : (Matrix ι ι (PowerSeries K))ˣ,
      (U : Matrix ι ι (PowerSeries K)) = 1 - zMatrix M ∧
      (↑(U⁻¹) : Matrix ι ι (PowerSeries K)) = geometricSeries M ∧
      ∀ i j : ι, (↑(U⁻¹) : Matrix ι ι (PowerSeries K)) i j =
        (((polynomialResolvent M).adjugate i j : Polynomial K) : PowerSeries K) *
          (((polynomialResolvent M).det : Polynomial K) : PowerSeries K)⁻¹ := by
  obtain ⟨U, hU, hInv⟩ := geometric_inverse M
  refine ⟨U, hU, hInv, ?_⟩
  intro i j
  rw [hInv]
  exact geometric_entry_adjugate M i j

end FiniteCombinatorics.Transfer
