import MathGenome.Internal.Specs.D05.M14.QrCholesky.Cholesky
import MathGenome.Internal.D05.M14.PositiveRoot
import MathGenome.Internal.D05.M14.QrCholesky.Qr

noncomputable section

namespace D05.M14.QrCholesky.Cholesky
open D05.QrCholesky
open scoped Matrix ComplexOrder

/-- Transport the upstream positive operator root through standard Euclidean
coordinates. Its square is invertible, so the root itself is invertible. -/
theorem invertible_positive_root :
    Specs.D05.M14.QrCholesky.Cholesky.invertible_positive_root := by
  intro F _ n H hH
  let T := H.toEuclideanLin
  have hp : D05.positiveSemidefinite T :=
    (D05.M14.Positive.positiveSemidefinite_iff_mathlib T).mpr
      (Matrix.isPositive_toEuclideanLin_iff.mpr hH.posSemidef)
  obtain ⟨S, hS, hsq⟩ := D05.M14.PositiveRoot.exists_positive_root T hp
  let A := Matrix.toEuclideanLin.symm S
  have ha : A.toEuclideanLin = S := Matrix.toEuclideanLin.apply_symm_apply S
  have hpa : A.PosSemidef := Matrix.isPositive_toEuclideanLin_iff.mp
    (by rw [ha]; exact (D05.M14.Positive.positiveSemidefinite_iff_mathlib S).mp hS)
  have hsqA : A ^ 2 = H := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_pow, ha]
    exact hsq
  have hu : IsUnit A := (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    (by rw [hsqA]; exact hH.isUnit)
  exact ⟨A, hpa, hu, (pow_two A).symm.trans hsqA⟩

/-- Euclidean columns of an invertible square matrix are independent. -/
theorem fullColumnRank_of_isUnit {F : Type*} [RCLike F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : IsUnit A) : FullColumnRank A := by
  let e := (WithLp.linearEquiv 2 F (Fin n → F)).symm
  exact (Matrix.linearIndependent_col_iff_isUnit.mpr hA).map'
    e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)

theorem existence : Specs.D05.M14.QrCholesky.Cholesky.existence := by
  intro F _ n H hH
  obtain ⟨S, hS, hu, hs⟩ := invertible_positive_root H hH
  obtain ⟨⟨Q, R⟩, hqr, _⟩ :=
    D05.M14.QrCholesky.Qr.exists_unique_reduced_qr S (fullColumnRank_of_isUnit S hu)
  obtain ⟨he, hQ, hR, hp⟩ := hqr
  refine ⟨R, ?_, hR, hp⟩
  calc
    H = S.conjTranspose * S := by rw [hS.isHermitian.eq]; exact hs.symm
    _ = R.conjTranspose * R := by
      rw [he, Matrix.conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc Q.conjTranspose Q R, hQ, Matrix.one_mul]

/-- The transition R₁ R₂⁻¹ is upper triangular, unitary, and positive on the
real diagonal. The upstream triangular-unitary theorem therefore makes it I. -/
theorem uniqueness : Specs.D05.M14.QrCholesky.Cholesky.uniqueness := by
  intro F _ n H R₁ R₂ h₁ h₂
  obtain ⟨he₁, ht₁, hp₁⟩ := h₁
  obtain ⟨he₂, ht₂, hp₂⟩ := h₂
  obtain ⟨_, hti, hiL, hiR⟩ := D05.M14.QrCholesky.Qr.triangular_inverses R₂ ht₂ hp₂
  let C := R₁ * R₂⁻¹
  have ht : C.IsUpperTriangular := ht₁.mul hti
  have hCR : R₁ = C * R₂ := by
    dsimp [C]
    rw [Matrix.mul_assoc, hiL, Matrix.mul_one]
  have hp : ∀ i, ∃ r : ℝ, 0 < r ∧ C i i = (r : F) := by
    intro i
    obtain ⟨r, hr, her⟩ := hp₁ i
    obtain ⟨s, hs, hes⟩ := hp₂ i
    have hd : (r : F) = C i i * (s : F) := by
      rw [← her, hCR, D05.M14.QrCholesky.Qr.upper_triangular_mul_diag C R₂ ht ht₂, hes]
    refine ⟨r / s, div_pos hr hs, ?_⟩
    rw [RCLike.ofReal_div]
    exact (eq_div_iff (by exact_mod_cast ne_of_gt hs)).mpr hd.symm
  have hu : C.conjTranspose * C = 1 := by
    calc
      C.conjTranspose * C =
          R₂⁻¹.conjTranspose * (R₁.conjTranspose * R₁) * R₂⁻¹ := by
        simp only [C, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = R₂⁻¹.conjTranspose * (R₂.conjTranspose * R₂) * R₂⁻¹ := by rw [← he₁, he₂]
      _ = R₂⁻¹.conjTranspose * R₂.conjTranspose * (R₂ * R₂⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hiR, Matrix.mul_one, ← Matrix.conjTranspose_mul, hiR, Matrix.conjTranspose_one]
  have hC := D05.M14.QrCholesky.TriangularUnitary.positive_diagonal_unitary C ht hu hp
  simpa only [hC, Matrix.one_mul] using hCR

theorem exists_unique_cholesky :
    Specs.D05.M14.QrCholesky.Cholesky.exists_unique_cholesky := by
  intro F _ n H hH
  obtain ⟨R, hR⟩ := existence H hH
  exact ⟨R, hR, fun S hS => uniqueness H S R hS hR⟩

theorem zero_dimension : Specs.D05.M14.QrCholesky.Cholesky.zero_dimension := by
  intro F _ H
  have hH : H = 1 := Subsingleton.elim _ _
  refine ⟨hH ▸ Matrix.PosDef.one, Subsingleton.elim _ _, ?_, ?_, fun R => Subsingleton.elim _ _⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

end D05.M14.QrCholesky.Cholesky
