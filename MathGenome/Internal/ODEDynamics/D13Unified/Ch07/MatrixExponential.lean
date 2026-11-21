import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.MatrixExponential

noncomputable section

-- This auxiliary matrix norm is used only to apply Banach-algebra convergence.
-- The public norm for a fixed state space is `matrixOperatorNorm`.
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch07

variable {𝕂 n : Type*} [RCLike 𝕂] [Fintype n] [DecidableEq n]

/-- The matrix exponential, with real time for both real and complex entries. -/
def matrixExp (A : Matrix n n 𝕂) (t : ℝ) : Matrix n n 𝕂 :=
  NormedSpace.exp (t • A)

theorem matrixExp_hasSum (A : Matrix n n 𝕂) (t : ℝ) :
    HasSum (fun j : ℕ => (t ^ j / (Nat.factorial j : ℝ)) • A ^ j) (matrixExp A t) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • A)
  simpa only [smul_pow, smul_smul, div_eq_mul_inv, mul_comm, matrixExp] using h

/-- Equality with the series printed in Chapter 7. -/
theorem matrixExp_eq_tsum (A : Matrix n n 𝕂) (t : ℝ) :
    matrixExp A t = ∑' j : ℕ, (t ^ j / (Nat.factorial j : ℝ)) • A ^ j :=
  (matrixExp_hasSum A t).tsum_eq.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [FiniteDimensional 𝕂 E]

theorem matrixOperator_action (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂) (x : E) :
    b.equivFun (matrixOperatorEquiv b A x) = A.mulVec (b.equivFun x) := by
  change b.equivFun (b.equivFun.symm (A.mulVec (b.equivFun x))) = _
  exact b.equivFun.apply_symm_apply _

theorem matrixOperator_norm_apply (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂) (x : E) :
    ‖matrixOperatorEquiv b A x‖ ≤ matrixOperatorNorm b A * ‖x‖ :=
  (matrixOperatorEquiv b A).le_opNorm x

theorem matrixOperator_exp (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂) (t : ℝ) :
    matrixOperatorEquiv b (matrixExp A t) =
      NormedSpace.exp ((algebraMap ℝ 𝕂 t) • matrixOperatorEquiv b A) := by
  let := Algebra.restrictScalars ℚ 𝕂 (E →L[𝕂] E)
  have h := NormedSpace.map_exp (matrixOperatorEquiv b)
    (matrixOperatorEquiv b).toLinearMap.continuous_of_finiteDimensional (t • A)
  change matrixOperatorEquiv b (NormedSpace.exp (t • A)) = _
  rw [h, ← algebraMap_smul 𝕂 t A, map_smul]

end D13Unified.Ch07
