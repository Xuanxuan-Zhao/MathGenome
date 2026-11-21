import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.GeneratingSeries
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Transfer.GeometricMatrixSeries

/-! The coefficientwise geometric inverse of a finite matrix (p204:W17). -/

noncomputable section

universe u v

namespace FiniteCombinatorics.Transfer

/-- The matrix `zM`, represented by power series in each entry. -/
def zMatrix {R : Type u} [CommRing R] {ι : Type v}
    (M : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  fun i j => PowerSeries.X * PowerSeries.C (M i j)

/-- `∑ n ≥ 0, M^n z^n`, interpreted entrywise using the canonical OGF. -/
def geometricSeries {R : Type u} [CommRing R] {ι : Type v}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    Matrix ι ι (PowerSeries R) :=
  fun i j => Series.ogf (fun n => (M ^ n) i j)

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

@[simp]
theorem coeff_geometricSeries (M : Matrix ι ι R) (n : ℕ) (i j : ι) :
    PowerSeries.coeff n (geometricSeries M i j) = (M ^ n) i j :=
  Series.coeff_ogf _ _

omit [DecidableEq ι] in
private theorem coeff_zMatrix_mul (M : Matrix ι ι R)
    (A : Matrix ι ι (PowerSeries R)) (n : ℕ) (i j : ι) :
    PowerSeries.coeff (n + 1) ((zMatrix M * A) i j) =
      ∑ k, M i k * PowerSeries.coeff n (A k j) := by
  simp only [Matrix.mul_apply, zMatrix, map_sum, mul_assoc,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]

omit [DecidableEq ι] in
private theorem coeff_mul_zMatrix (M : Matrix ι ι R)
    (A : Matrix ι ι (PowerSeries R)) (n : ℕ) (i j : ι) :
    PowerSeries.coeff (n + 1) ((A * zMatrix M) i j) =
      ∑ k, PowerSeries.coeff n (A i k) * M k j := by
  simp only [Matrix.mul_apply, zMatrix, map_sum, ← mul_assoc,
    PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X]

theorem resolvent_mul_geometric (M : Matrix ι ι R) :
    (1 - zMatrix M) * geometricSeries M = 1 := by
  rw [sub_mul, one_mul]
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [Matrix.sub_apply, Matrix.mul_apply, zMatrix, geometricSeries,
        Series.ogf, Matrix.one_apply]
  | succ n =>
      simp only [Matrix.sub_apply, map_sub, coeff_geometricSeries,
        coeff_zMatrix_mul, ← Matrix.mul_apply, ← pow_succ', sub_self]
      by_cases h : i = j <;> simp [Matrix.one_apply, h, PowerSeries.coeff_one]

theorem geometric_mul_resolvent (M : Matrix ι ι R) :
    geometricSeries M * (1 - zMatrix M) = 1 := by
  rw [mul_sub, mul_one]
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [Matrix.sub_apply, Matrix.mul_apply, zMatrix, geometricSeries,
        Series.ogf, Matrix.one_apply]
  | succ n =>
      simp only [Matrix.sub_apply, map_sub, coeff_geometricSeries,
        coeff_mul_zMatrix, ← Matrix.mul_apply, ← pow_succ, sub_self]
      by_cases h : i = j <;> simp [Matrix.one_apply, h, PowerSeries.coeff_one]

/-- Over any commutative ring the resolvent is a unit and its inverse is the
geometric series. This also covers the empty matrix. -/
theorem geometric_inverse (M : Matrix ι ι R) :
    ∃ U : (Matrix ι ι (PowerSeries R))ˣ,
      (U : Matrix ι ι (PowerSeries R)) = 1 - zMatrix M ∧
      (↑(U⁻¹) : Matrix ι ι (PowerSeries R)) = geometricSeries M := by
  exact ⟨⟨1 - zMatrix M, geometricSeries M,
    resolvent_mul_geometric M, geometric_mul_resolvent M⟩, rfl, rfl⟩

end FiniteCombinatorics.Transfer
