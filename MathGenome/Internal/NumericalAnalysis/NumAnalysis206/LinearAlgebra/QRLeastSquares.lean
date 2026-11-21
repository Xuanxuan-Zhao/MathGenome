import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.QRLeastSquares
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.ReducedQR
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.NormalEquations

noncomputable section
namespace NumAnalysis206.QRLeastSquares
open MatrixDefinitions

variable {K : Type*} [RCLike K] {m n : ℕ}

/-- The genuine triangular inverse gives the fitted-vector formula, including
when the column space has dimension zero. -/
theorem fitted_vector_eq (A Q : Mat K m n) (R : Mat K n n)
    (hQR : ReducedQR A Q R) (b : Vec K m) :
    A.toEuclideanLin (R⁻¹.toEuclideanLin ((adjoint Q).toEuclideanLin b)) =
      Q.toEuclideanLin ((adjoint Q).toEuclideanLin b) := by
  obtain ⟨hfac, _, htri, hpos⟩ := hQR
  obtain ⟨_, _, _, hright⟩ := D05.M14.QrCholesky.Qr.triangular_inverses R htri hpos
  have hmap : A.toEuclideanLin.comp R⁻¹.toEuclideanLin = Q.toEuclideanLin := by
    rw [← MatrixData.toEuclidean_mul, hfac, Matrix.mul_assoc, hright, Matrix.mul_one]
  exact LinearMap.congr_fun hmap _

/-- Q* annihilates the residual of the proposed solution. -/
theorem qr_formula_normal (A Q : Mat K m n) (R : Mat K n n)
    (hQR : ReducedQR A Q R) (b : Vec K m) :
    LinearMap.adjoint A.toEuclideanLin
      (A.toEuclideanLin (R⁻¹.toEuclideanLin ((adjoint Q).toEuclideanLin b)) - b) = 0 := by
  have hq : (adjoint Q).toEuclideanLin.comp Q.toEuclideanLin = LinearMap.id := by
    rw [← MatrixData.toEuclidean_mul, adjoint, hQR.2.1]
    simp
  have hr : (adjoint Q).toEuclideanLin
      (Q.toEuclideanLin ((adjoint Q).toEuclideanLin b) - b) = 0 := by
    rw [map_sub, ← LinearMap.comp_apply, hq, LinearMap.id_apply, sub_self]
  rw [fitted_vector_eq A Q R hQR b, ← MatrixData.toEuclidean_adjoint,
    adjoint, hQR.1, Matrix.conjTranspose_mul, MatrixData.toEuclidean_mul]
  change (adjoint R).toEuclideanLin
    ((adjoint Q).toEuclideanLin (Q.toEuclideanLin ((adjoint Q).toEuclideanLin b) - b)) = 0
  rw [hr, map_zero]

theorem minimizer_iff_qr_formula :
    Specs.NumAnalysis206.QRLeastSquares.minimizer_iff_qr_formula := by
  intro K _ m n A Q R hA hQR b x
  have hmin := (NormalEquations.minimizer_iff_normal_equation A.toEuclideanLin b
    (R⁻¹.toEuclideanLin ((adjoint Q).toEuclideanLin b))).mpr
      (qr_formula_normal A Q R hQR b)
  obtain ⟨z, hz, huniq⟩ := NormalEquations.exists_unique_injective_minimizer
    A.toEuclideanLin ((MatrixData.fullColumnRank_iff_injective A).mp hA) b
  constructor
  · intro hx
    exact (huniq x hx).trans (huniq _ hmin).symm
  · rintro rfl
    exact hmin

theorem exists_unique_qr_minimizer :
    Specs.NumAnalysis206.QRLeastSquares.exists_unique_qr_minimizer := by
  intro K _ m n A Q R hA hQR b
  have hmin := (minimizer_iff_qr_formula A Q R hA hQR b _).mpr rfl
  exact ⟨hmin, _, hmin, fun x hx => (minimizer_iff_qr_formula A Q R hA hQR b x).mp hx⟩

theorem fitted_vector_eq_projection :
    Specs.NumAnalysis206.QRLeastSquares.fitted_vector_eq_projection := by
  intro K _ m n A Q R hA hQR b
  refine ⟨fitted_vector_eq A Q R hQR b, ?_⟩
  rw [← fitted_vector_eq A Q R hQR b]
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact LinearMap.mem_range_self _ _
  · intro w hw
    obtain ⟨y, rfl⟩ := hw
    have hn := qr_formula_normal A Q R hQR b
    rw [← neg_sub, inner_neg_left, ← LinearMap.adjoint_inner_left, hn]
    simp

end NumAnalysis206.QRLeastSquares
