import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.PositiveCholesky
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.D05.M14.QrCholesky.Cholesky

noncomputable section
open scoped ComplexOrder
namespace NumAnalysis206.PositiveCholesky
open MatrixData

/-- The canonical diagonal condition is preserved by conjugate transpose. -/
theorem positiveRealDiagonal_adjoint {K : Type*} [RCLike K] {n : ℕ}
    {R : Mat K n n} (hR : PositiveRealDiagonal R) :
    PositiveRealDiagonal (adjoint R) := by
  intro i
  obtain ⟨r, hr, he⟩ := hR i
  refine ⟨r, hr, ?_⟩
  simp [adjoint, NumAnalysis206.MatrixDefinitions.adjoint,
    Matrix.conjTranspose_apply, he]

/-- Reuse the full Cholesky theorem with the accepted matrix conventions. -/
theorem upper_unique : Specs.NumAnalysis206.PositiveCholesky.upper_unique := by
  intro K _ n A hA
  obtain ⟨R, ⟨he, ht, hp⟩, hu⟩ :=
    D05.M14.QrCholesky.Cholesky.exists_unique_cholesky A hA
  refine ⟨R, ⟨he, (fun i j hij => ht hij), hp⟩, ?_⟩
  rintro S ⟨heS, htS, hpS⟩
  exact hu S ⟨heS, (fun {i j} hij => htS i j hij), hpS⟩

theorem lower_of_upper : Specs.NumAnalysis206.PositiveCholesky.lower_of_upper := by
  intro K _ n A R hR
  obtain ⟨he, ht, hp⟩ := hR
  refine ⟨?_, ?_, positiveRealDiagonal_adjoint hp⟩
  · simpa only [NumAnalysis206.MatrixDefinitions.adjoint,
      Matrix.conjTranspose_conjTranspose] using he
  · intro i j hij
    change star (R j i) = 0
    rw [ht j i hij, star_zero]

/-- Adjoint is an involution, so uniqueness of upper factors also proves
uniqueness among all eligible lower factors. -/
theorem lower_unique : Specs.NumAnalysis206.PositiveCholesky.lower_unique := by
  intro K _ n A hA
  obtain ⟨R, hR, hu⟩ := upper_unique A hA
  refine ⟨adjoint R, lower_of_upper A R hR, ?_⟩
  rintro L ⟨he, ht, hp⟩
  have hL : A = adjoint (adjoint L) * adjoint L ∧
      IsUpperTriangular (adjoint L) ∧ PositiveRealDiagonal (adjoint L) := by
    refine ⟨?_, ?_, positiveRealDiagonal_adjoint hp⟩
    · simpa only [adjoint, NumAnalysis206.MatrixDefinitions.adjoint,
        Matrix.conjTranspose_conjTranspose] using he
    · intro i j hij
      change star (L j i) = 0
      rw [ht j i hij, star_zero]
  have h := congrArg (fun M : Mat K n n => adjoint M) (hu (adjoint L) hL)
  simpa only [adjoint, NumAnalysis206.MatrixDefinitions.adjoint,
    Matrix.conjTranspose_conjTranspose] using h

end NumAnalysis206.PositiveCholesky
