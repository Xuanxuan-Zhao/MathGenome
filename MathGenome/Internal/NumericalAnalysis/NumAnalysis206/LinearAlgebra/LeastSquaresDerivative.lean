import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.LeastSquaresDerivative
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.NormalEquations
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The joint chain rule differentiates the inverse Gram operator and its
 application to `A* b`. Expanding the resulting derivative and collecting its
 terms gives the residual formula. Unit openness gives persistence of rank.
 Neither argument assumes a nonzero-dimensional domain. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
open NumAnalysis206.MatrixDefinitions NumAnalysis206.LeastSquaresDefinitions
namespace NumAnalysis206.LeastSquaresDerivative

private def operatorMap {m n : ℕ} : Mat ℝ m n →L[ℝ] (Vec ℝ n →L[ℝ] Vec ℝ m) :=
  ((LinearMap.toContinuousLinearMap :
      (Vec ℝ n →ₗ[ℝ] Vec ℝ m) ≃ₗ[ℝ] (Vec ℝ n →L[ℝ] Vec ℝ m)).toLinearMap.comp
    Matrix.toEuclideanLin.toLinearMap).toContinuousLinearMap

@[simp] private theorem operatorMap_apply {m n : ℕ} (A : Mat ℝ m n) :
    operatorMap A = operator A := rfl

private theorem gram_isUnit {m n : ℕ} (A : Mat ℝ m n) (hA : FullColumnRank A) :
    IsUnit (gram A) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  simpa [gram, operator, ← LinearMap.adjoint_toContinuousLinearMap] using
    NormalEquations.gram_isUnit_of_injective A.toEuclideanLin
      ((MatrixData.fullColumnRank_iff_injective A).mp hA)

theorem gram_invertible : Specs.NumAnalysis206.LeastSquaresDerivative.gram_invertible := by
  intro m n A hA
  have h := gram_isUnit A hA
  exact ⟨h, Ring.inverse_mul_cancel _ h, Ring.mul_inverse_cancel _ h⟩

theorem solution_eq_normal_formula :
    Specs.NumAnalysis206.LeastSquaresDerivative.solution_eq_normal_formula := by
  intro m n A b hA
  have hi := (gram_isUnit A hA).map_ringInverse
    (ContinuousLinearMap.toLinearMapRingHom :
      (Vec ℝ n →L[ℝ] Vec ℝ n) →+* (Vec ℝ n →ₗ[ℝ] Vec ℝ n))
  have hInv : (inverseGram A).toLinearMap =
      Ring.inverse ((LinearMap.adjoint A.toEuclideanLin).comp A.toEuclideanLin) := by
    simpa [inverseGram, gram, operator, ← LinearMap.adjoint_toContinuousLinearMap] using hi
  change (inverseGram A).toLinearMap ((operator A).adjoint b) = _
  rw [hInv]
  simp [operator, ← LinearMap.adjoint_toContinuousLinearMap]

private def adjointMap {m n : ℕ} :
    (Vec ℝ n →L[ℝ] Vec ℝ m) →L[ℝ] (Vec ℝ m →L[ℝ] Vec ℝ n) :=
  ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] private theorem adjointMap_apply {m n : ℕ}
    (A : Vec ℝ n →L[ℝ] Vec ℝ m) : adjointMap A = A.adjoint := rfl

private theorem gram_differentiable {m n : ℕ} :
    Differentiable ℝ (gram : Mat ℝ m n → (Vec ℝ n →L[ℝ] Vec ℝ n)) := by
  intro A
  exact (((adjointMap (m := m) (n := n)).differentiableAt.comp A
    operatorMap.differentiableAt).clm_comp operatorMap.differentiableAt)

theorem fullColumnRank_nearby :
    Specs.NumAnalysis206.LeastSquaresDerivative.fullColumnRank_nearby := by
  intro m n A hA
  have h : ∀ᶠ B in nhds A, IsUnit (gram B) :=
    (gram_differentiable.continuous.continuousAt).eventually
      (Units.isOpen.mem_nhds (gram_isUnit A hA))
  filter_upwards [h] with B hB
  apply (MatrixData.fullColumnRank_iff_injective B).mpr
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp hB).injective
  have hj : Function.Injective (operator B) :=
    (ContinuousLinearMap.adjoint_comp_self_injective_iff (operator B)).mp hi
  exact hj

theorem hasFDerivAt_solution :
    Specs.NumAnalysis206.LeastSquaresDerivative.hasFDerivAt_solution := by
  intro m n A b hA
  let P := Mat ℝ m n × Vec ℝ m
  let a' : P →L[ℝ] (Vec ℝ n →L[ℝ] Vec ℝ m) :=
    operatorMap.comp (ContinuousLinearMap.fst ℝ _ _)
  have ha : HasFDerivAt (fun p : P => operator p.1) a' (A, b) :=
    operatorMap.hasFDerivAt.comp (A, b) hasFDerivAt_fst
  have hadj := adjointMap.hasFDerivAt.comp (A, b) ha
  have hg := hadj.clm_comp ha
  obtain ⟨u, hu⟩ := gram_isUnit A hA
  have huinv : (↑u⁻¹ : Vec ℝ n →L[ℝ] Vec ℝ n) = inverseGram A := by
    simp [inverseGram, ← hu]
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hinv
  have hx := (hinv.comp (A, b) hg).clm_apply (hadj.clm_apply hasFDerivAt_snd)
  refine ⟨_, hx, ?_⟩
  intro E f
  simp [huinv, a', P, leftInverse, inverseGram, solution, LeastSquaresDefinitions.residual, gram,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.compL_apply]
  abel

end NumAnalysis206.LeastSquaresDerivative
