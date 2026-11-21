import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.ExponentialCalculus
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.NilpotentInstability
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section

open scoped Matrix.Norms.Operator

namespace D13Unified.Ch07

variable {𝕂 : Type*} [RCLike 𝕂]

theorem nilpotentMatrix_sq : (nilpotentMatrix 𝕂) ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [nilpotentMatrix, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem nilpotentMatrix_pow (j : ℕ) (hj : 2 ≤ j) :
    (nilpotentMatrix 𝕂) ^ j = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [pow_add, nilpotentMatrix_sq, zero_mul]

theorem nilpotent_exp (t : ℝ) :
    matrixExp (nilpotentMatrix 𝕂) t = !![1, algebraMap ℝ 𝕂 t; 0, 1] := by
  have hfinite : HasSum
      (fun j : ℕ => (t ^ j / (Nat.factorial j : ℝ)) • (nilpotentMatrix 𝕂) ^ j)
      (∑ j ∈ Finset.range 2,
        (t ^ j / (Nat.factorial j : ℝ)) • (nilpotentMatrix 𝕂) ^ j) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hge : 2 ≤ j := Nat.le_of_not_lt (fun h => hj (Finset.mem_range.mpr h))
    rw [nilpotentMatrix_pow j hge, smul_zero]
  have h := (matrixExp_hasSum (nilpotentMatrix 𝕂) t).unique hfinite
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Finset.sum_range_succ, nilpotentMatrix, RCLike.real_smul_eq_coe_mul]

theorem nilpotent_eigenvalue (μ : 𝕂) :
    Module.End.HasEigenvalue (Matrix.toLin' (nilpotentMatrix 𝕂)) μ ↔ μ = 0 := by
  constructor
  · intro hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have heq := hv.apply_eq_smul
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      nilpotentMatrix] at h0 h1
    by_contra hne
    have hv1 : v 1 = 0 := h1.resolve_left hne
    have hv0 : v 0 = 0 := by
      rw [hv1] at h0
      exact (mul_eq_zero.mp h0.symm).resolve_left hne
    apply hv.2
    ext i
    fin_cases i <;> assumption
  · rintro rfl
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, 0])
    constructor
    · apply Module.End.mem_eigenspace_iff.mpr
      ext i
      fin_cases i <;>
        simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          nilpotentMatrix]
    · intro h
      have h0 := congrFun h 0
      norm_num at h0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- In coordinates the global solution is the shear `(x₁ + t x₂, x₂)`. -/
theorem nilpotentFlow_coordinates (b : Module.Basis (Fin 2) ℝ E) (x : E) (t : ℝ) :
    b.equivFun (nilpotentFlow b x t) =
      ![b.equivFun x 0 + t * b.equivFun x 1, b.equivFun x 1] := by
  change b.equivFun (matrixOperatorEquiv b (matrixExp (nilpotentMatrix ℝ) t) x) = _
  rw [matrixOperator_action, nilpotent_exp]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem nilpotentFlow_eq (b : Module.Basis (Fin 2) ℝ E) (x : E) (t : ℝ) :
    nilpotentFlow b x t = x + t • (b.equivFun x 1 • b 0) := by
  apply b.equivFun.injective
  rw [nilpotentFlow_coordinates, map_add, map_smul, map_smul]
  ext i
  fin_cases i <;> simp

theorem nilpotentMatrix_action (b : Module.Basis (Fin 2) ℝ E) (x : E) :
    matrixOperatorEquiv b (nilpotentMatrix ℝ) x = b.equivFun x 1 • b 0 := by
  apply b.equivFun.injective
  rw [matrixOperator_action, map_smul]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    nilpotentMatrix]

theorem nilpotent_solution (b : Module.Basis (Fin 2) ℝ E) (x : E) :
    nilpotentFlow b x 0 = x ∧ ContDiff ℝ 1 (nilpotentFlow b x) ∧
      ∀ t : ℝ, HasDerivAt (nilpotentFlow b x)
        (matrixOperatorEquiv b (nilpotentMatrix ℝ) (nilpotentFlow b x t)) t := by
  have hf : nilpotentFlow b x = fun s : ℝ => x + s • (b.equivFun x 1 • b 0) :=
    funext (nilpotentFlow_eq b x)
  refine ⟨?_, ?_, ?_⟩
  · simp [nilpotentFlow_eq]
  · rw [hf]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  · intro t
    rw [nilpotentMatrix_action, nilpotentFlow_coordinates]
    change HasDerivAt (nilpotentFlow b x) (b.equivFun x 1 • b 0) t
    rw [hf]
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id t).smul_const (b.equivFun x 1 • b 0)).const_add x

omit [FiniteDimensional ℝ E] in
/-- A continuous coordinate functional controls the first coordinate in any
fixed state norm. The added one makes the constant strictly positive. -/
theorem basis_firstCoordinate_norm_le (b : Module.Basis (Fin 2) ℝ E) (x : E) :
    ‖b.equivFun x 0‖ ≤ (‖b.equivFunL.toContinuousLinearMap‖ + 1) * ‖x‖ := by
  calc
    ‖b.equivFun x 0‖ ≤ ‖b.equivFun x‖ := norm_le_pi_norm _ _
    _ ≤ ‖b.equivFunL.toContinuousLinearMap‖ * ‖x‖ :=
      b.equivFunL.toContinuousLinearMap.le_opNorm x
    _ ≤ (‖b.equivFunL.toContinuousLinearMap‖ + 1) * ‖x‖ := by
      nlinarith [norm_nonneg x]

theorem nilpotent_escape (b : Module.Basis (Fin 2) ℝ E) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧ ‖η • b 1‖ < δ ∧
        0 ≤ 1 / η ∧
        b.equivFun (nilpotentFlow b (η • b 1) (1 / η)) 0 = 1 ∧
        ε₀ ≤ ‖nilpotentFlow b (η • b 1) (1 / η)‖ := by
  let C : ℝ := ‖b.equivFunL.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨1 / C, one_div_pos.mpr hC, ?_⟩
  intro δ hδ
  let η : ℝ := δ / (2 * (‖b 1‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * (2 * (‖b 1‖ + 1)) = δ :=
    div_mul_cancel₀ δ (by positivity)
  have hsmall : ‖η • b 1‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    nlinarith [norm_nonneg (b 1)]
  have hfirst : b.equivFun (nilpotentFlow b (η • b 1) (1 / η)) 0 = 1 := by
    rw [nilpotentFlow_coordinates]
    simp [map_smul, hη.ne']
  refine ⟨η, hη, hsmall, le_of_lt (one_div_pos.mpr hη), hfirst, ?_⟩
  have hbound := basis_firstCoordinate_norm_le b (nilpotentFlow b (η • b 1) (1 / η))
  rw [hfirst, norm_one] at hbound
  exact (div_le_iff₀ hC).mpr (by simpa [mul_comm] using hbound)

theorem nilpotent_unbounded (b : Module.Basis (Fin 2) ℝ E) (M : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ M < ‖nilpotentFlow b (b 1) t‖ := by
  let C : ℝ := ‖b.equivFunL.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let t : ℝ := C * (|M| + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨t, ht.le, ?_⟩
  have hbound := basis_firstCoordinate_norm_le b (nilpotentFlow b (b 1) t)
  have hfirst : b.equivFun (nilpotentFlow b (b 1) t) 0 = t := by
    rw [nilpotentFlow_coordinates]
    simp
  rw [hfirst, Real.norm_eq_abs, abs_of_pos ht] at hbound
  change t ≤ C * ‖nilpotentFlow b (b 1) t‖ at hbound
  have hle : |M| + 1 ≤ ‖nilpotentFlow b (b 1) t‖ :=
    (mul_le_mul_iff_right₀ hC).mp hbound
  linarith [le_abs_self M]

end D13Unified.Ch07
