import MathGenome.Internal.Specs.D05.M08.NewtonIdentities.Series
import MathGenome.Internal.D05.M05.Adjugate
import Mathlib.Tactic.Ring

noncomputable section
open PowerSeries Matrix Finset
namespace D05.M08.NewtonIdentities.Series

private theorem derivative_prod {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → K⟦X⟧) :
    derivative (∏ i ∈ s, f i) =
      ∑ i ∈ s, derivative (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha]
    simp only [smul_eq_mul, erase_insert ha]
    rw [mul_sum, add_comm]
    congr 1
    · ring
    · apply sum_congr rfl
      intro i hi
      have hia : i ≠ a := ne_of_mem_of_not_mem hi ha
      rw [Finset.erase_insert_of_ne hia.symm, prod_insert (notMem_mono (erase_subset i s) ha)]
      ring

/-- Jacobi's formula, proved by the finite Leibniz expansion. -/
private theorem derivative_det_rows {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K⟦X⟧) :
    derivative M.det = ∑ i, (M.updateRow i (fun j => derivative (M i j))).det := by
  rw [← det_transpose, det_apply']
  simp only [map_sum, Derivation.leibniz, smul_eq_mul]
  simp only [show ∀ z : ℤ, derivative (z : K⟦X⟧) = 0 by intro z; exact Derivation.map_intCast _ z,
    mul_zero, add_zero, derivative_prod]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← det_transpose, det_apply']
  apply sum_congr rfl
  intro σ _
  rw [← Finset.mul_prod_erase _ _ (mem_univ i)]
  simp only [transpose_apply, updateRow_self]
  have hprod : (∏ j ∈ univ.erase i, (M.updateRow i (fun j => derivative (M i j))) j (σ j)) =
      ∏ j ∈ univ.erase i, M j (σ j) := by
    apply prod_congr rfl
    intro j hj
    simp only [mem_erase] at hj
    simp [Matrix.updateRow_ne hj.1]
  rw [hprod]

private theorem det_updateRow_eq_sum {R : Type*} [CommRing R] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (i : ι) (v : ι → R) :
    (M.updateRow i v).det = ∑ j, v j * M.adjugate j i := by
  rw [← cramer_transpose_apply]
  conv_lhs => rw [pi_eq_sum_univ' v, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply sum_congr rfl
  intro j _
  rw [cramer_transpose_apply, ← adjugate_apply]

private theorem derivative_det {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K⟦X⟧) :
    derivative M.det = Matrix.trace (M.adjugate * M.map derivative) := by
  rw [derivative_det_rows]
  simp_rw [det_updateRow_eq_sum]
  simp only [Matrix.trace, Matrix.diag_apply]
  simp only [Matrix.mul_apply, Matrix.map_apply]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  exact mul_comm _ _

variable {K : Type*} [Field K] {n : ℕ}

/-- The requested series construction, with the independent coefficient definition. -/
def geometricMatrix : Specs.D05.M08.NewtonIdentities.Series.geometricMatrix_type :=
  Specs.D05.M08.NewtonIdentities.Series.geometricMatrix_value

theorem coefficients : Specs.D05.M08.NewtonIdentities.Series.coefficients := by
  intro K _ n A j i k
  exact coeff_mk j _

private theorem coeff_constant_mul (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin n) K⟦X⟧) (j : ℕ) (i k : Fin n) :
    coeff j ((constantMatrix A * B) i k) =
      (A * (B.map (coeff j))) i k := by
  simp [Matrix.mul_apply, constantMatrix, coeff_C_mul]

private theorem coeff_mul_constant (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin n) K⟦X⟧) (j : ℕ) (i k : Fin n) :
    coeff j ((B * constantMatrix A) i k) =
      (B.map (coeff j) * A) i k := by
  simp [Matrix.mul_apply, constantMatrix, coeff_mul_C]

private theorem geometric_coeff_matrix (A : Matrix (Fin n) (Fin n) K) (j : ℕ) :
    (D05.M08.NewtonIdentities.geometricMatrix A).map (coeff j) = A ^ j := by
  apply Matrix.ext
  intro i k
  change coeff j (PowerSeries.mk (fun d => (A ^ d) i k)) = (A ^ j) i k
  exact coeff_mk j _

theorem inverse_left : Specs.D05.M08.NewtonIdentities.Series.inverse_left := by
  intro K _ n A
  rw [pencil, sub_mul, one_mul, Matrix.smul_mul]
  apply Matrix.ext
  intro i k
  apply PowerSeries.ext
  intro j
  cases j with
  | zero => simp [D05.M08.NewtonIdentities.geometricMatrix, Matrix.one_apply]
  | succ j =>
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
      coeff_succ_X_mul, coeff_constant_mul, geometric_coeff_matrix]
    rw [← pow_succ']
    simp [D05.M08.NewtonIdentities.geometricMatrix, Matrix.one_apply, apply_ite]

theorem inverse_right : Specs.D05.M08.NewtonIdentities.Series.inverse_right := by
  intro K _ n A
  rw [pencil, mul_sub, mul_one, Matrix.mul_smul]
  apply Matrix.ext
  intro i k
  apply PowerSeries.ext
  intro j
  cases j with
  | zero => simp [D05.M08.NewtonIdentities.geometricMatrix, Matrix.one_apply]
  | succ j =>
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
      coeff_succ_X_mul, coeff_mul_constant, geometric_coeff_matrix]
    rw [← pow_succ]
    simp [D05.M08.NewtonIdentities.geometricMatrix, Matrix.one_apply, apply_ite]

private theorem pencil_derivative (A : Matrix (Fin n) (Fin n) K) :
    (pencil A).map derivative = -constantMatrix A := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;>
    simp [pencil, constantMatrix, h, Derivation.leibniz, smul_eq_mul]

theorem determinant_derivative :
    Specs.D05.M08.NewtonIdentities.Series.determinant_derivative := by
  intro K _ n A
  rw [determinantSeries, D05.M05.DetDefinition.matrix_det_bridge, derivative_det,
    pencil_derivative, D05.M05.Adjugate.matrix_adjugate_bridge, Matrix.mul_neg, Matrix.trace_neg]

theorem adjugate_series : Specs.D05.M08.NewtonIdentities.Series.adjugate_series := by
  intro K _ n A
  rw [D05.M05.Adjugate.matrix_adjugate_bridge]
  calc
    (pencil A).adjugate = (pencil A).adjugate *
        (pencil A * D05.M08.NewtonIdentities.geometricMatrix A) := by
      rw [inverse_left A, mul_one]
    _ = determinantSeries A • D05.M08.NewtonIdentities.geometricMatrix A := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
      rw [determinantSeries, D05.M05.DetDefinition.matrix_det_bridge]

private theorem trace_geometric_mul (A : Matrix (Fin n) (Fin n) K) :
    Matrix.trace (D05.M08.NewtonIdentities.geometricMatrix A * constantMatrix A) =
      tracePowerSeries A := by
  apply PowerSeries.ext
  intro j
  simp only [Matrix.trace, Matrix.diag_apply, map_sum]
  simp_rw [coeff_mul_constant, geometric_coeff_matrix, ← pow_succ]
  change Matrix.trace (A ^ (j + 1)) = coeff j (mk (fun d => Matrix.trace (A ^ (d + 1))))
  rw [coeff_mk]

theorem logarithmic_derivative :
    Specs.D05.M08.NewtonIdentities.Series.logarithmic_derivative := by
  intro K _ n A
  rw [determinant_derivative A, adjugate_series A, Matrix.smul_mul, Matrix.trace_smul,
    trace_geometric_mul, smul_eq_mul, neg_mul]

theorem finite_coefficients : Specs.D05.M08.NewtonIdentities.Series.finite_coefficients := by
  intro K _ n A j
  have h := congrArg (coeff j) (logarithmic_derivative A)
  simpa only [coeff_derivative, map_neg, neg_mul, coeff_mul, Finset.sum_neg_distrib,
    tracePowerSeries, coeff_mk] using h

theorem empty_case : Specs.D05.M08.NewtonIdentities.Series.empty_case := by
  intro K _ A
  have hp : pencil A = 1 := Subsingleton.elim _ _
  have he : determinantSeries A = 1 := by rw [determinantSeries, D05.M05.DetDefinition.matrix_det_bridge, hp, Matrix.det_one]
  refine ⟨Subsingleton.elim _ _, hp, he, ?_, ?_⟩
  · apply PowerSeries.ext
    intro j
    simp [tracePowerSeries, Matrix.trace]
  · rw [he, PowerSeries.derivative_one]

end D05.M08.NewtonIdentities.Series
