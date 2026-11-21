import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.RankDeficientLeastSquares
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.D05.M14.LeastSquares
import MathGenome.Internal.D05.M14.SvdPseudoinverse

/-! W35: transport the finite-dimensional least-squares theorem and the
positive-singular-term formula to the canonical matrix pseudoinverse. -/
noncomputable section
open scoped BigOperators

namespace NumAnalysis206.RankDeficientLeastSquares
open MatrixData

theorem minimizers : Specs.NumAnalysis206.RankDeficientLeastSquares.minimizers := by
  intro K _ m n A b x
  rw [pseudoinverse_transport A]
  exact D05.M14.LeastSquares.minimizer_iff_exists_kernel A.toEuclideanLin b x

theorem pseudoinverse_minimizes :
    Specs.NumAnalysis206.RankDeficientLeastSquares.pseudoinverse_minimizes := by
  intro K _ m n A b y
  rw [pseudoinverse_transport A]
  exact D05.M14.LeastSquares.pseudoinverse_minimizes A.toEuclideanLin b y

theorem minimum_norm_unique :
    Specs.NumAnalysis206.RankDeficientLeastSquares.minimum_norm_unique := by
  intro K _ m n A b x hx
  rw [pseudoinverse_transport A]
  exact ⟨D05.M14.LeastSquares.minimum_norm A.toEuclideanLin b x hx,
    D05.M14.LeastSquares.norm_eq_iff A.toEuclideanLin b x hx⟩

theorem exists_svd : Specs.NumAnalysis206.RankDeficientLeastSquares.exists_svd := by
  intro K _ m n A
  exact D05.M14.Svd.exists_svd A.toEuclideanLin

theorem pseudoinverse_svd :
    Specs.NumAnalysis206.RankDeficientLeastSquares.pseudoinverse_svd := by
  intro K _ m n A d b
  rw [pseudoinverse_transport A]
  refine (D05.M14.SvdPseudoinverse.pseudoinverse_formula A.toEuclideanLin d b).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [NumAnalysis206.MatrixDefinitions.singularValue, Nat.add_sub_cancel]
  rfl

theorem pseudoinverse_rank_zero :
    Specs.NumAnalysis206.RankDeficientLeastSquares.pseudoinverse_rank_zero := by
  intro K _ m n A hA b
  obtain ⟨d⟩ := exists_svd A
  rw [pseudoinverse_svd A d b]
  have : IsEmpty (Fin (NumAnalysis206.MatrixDefinitions.rank A)) := by
    rw [hA]
    infer_instance
  exact Finset.sum_eq_zero (fun i _ => isEmptyElim i)

end NumAnalysis206.RankDeficientLeastSquares
