import MathGenome.Internal.Specs.D05.M08.Coefficients.AdjugateCoefficients
import MathGenome.Internal.D05.M05.Adjugate
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M04.Trace
import MathGenome.Internal.D05.M08.Coefficients.DeterminantDerivative
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Convert

noncomputable section
open scoped BigOperators
open Polynomial
namespace D05.M08.Coefficients.AdjugateCoefficients
open Specs.D05.M08.Coefficients.AdjugateCoefficients

variable {K : Type*} [Field K] {n : ℕ}

private theorem descending_expansion {R : Type*} [Semiring R]
    (f : Polynomial R) (d : ℕ) (h : f.natDegree ≤ d) :
    f = ∑ p ∈ Finset.range (d + 1), C (f.coeff (d - p)) * X ^ (d - p) := by
  have hr := Finset.sum_range_reflect (fun k => C (f.coeff k) * X ^ k) (d + 1)
  simp only [Nat.add_sub_cancel] at hr
  rw [hr]
  exact f.as_sum_range_C_mul_X_pow' (by omega)

private theorem determinant_degree (A : Matrix (Fin n) (Fin n) K) :
    (D05.M05.determinant (pencil A)).natDegree ≤ n := by
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  simpa [pencil] using Polynomial.natDegree_det_X_add_C_le
    (1 : Matrix (Fin n) (Fin n) K) A

theorem determinant_expansion :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.determinant_expansion := by
  intro K _ n A
  exact descending_expansion _ n (determinant_degree A)

theorem leading_coefficient :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.leading_coefficient := by
  intro K _ n A
  unfold e pencil
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  simpa using Polynomial.coeff_det_X_add_C_card (1 : Matrix (Fin n) (Fin n) K) A

private theorem adjugate_degree (A : Matrix (Fin n) (Fin n) K) (hn : 0 < n)
    (i j : Fin n) :
    (D05.M05.adjugate (pencil A) i j).natDegree ≤ n - 1 := by
  cases n with
  | zero => omega
  | succ m =>
    rw [D05.M05.Adjugate.matrix_adjugate_bridge,
      Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hm : (pencil A).submatrix j.succAbove i.succAbove =
        (X : Polynomial K) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix j.succAbove i.succAbove).map C +
        (A.submatrix j.succAbove i.succAbove).map C := by
      ext a b
      simp [pencil, Matrix.submatrix_apply, Matrix.one_apply]
    rw [hm]
    calc
      _ ≤ (Matrix.det ((X : Polynomial K) •
          ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix j.succAbove i.succAbove).map C +
          (A.submatrix j.succAbove i.succAbove).map C)).natDegree := by
        convert Polynomial.natDegree_C_mul_le ((-1 : K) ^ (j.val + i.val)) _ using 1; simp
      _ ≤ m := by
        simpa using (Polynomial.natDegree_det_X_add_C_le
          ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix j.succAbove i.succAbove)
          (A.submatrix j.succAbove i.succAbove))

theorem determinant_coefficient_bound :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.determinant_coefficient_bound := by
  intro K _ n A r hr
  exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (determinant_degree A) hr)

theorem adjugate_coefficient_bound :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.adjugate_coefficient_bound := by
  intro K _ n A hn r i j hr
  exact coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (adjugate_degree A hn i j) (by omega))

theorem adjugate_expansion :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.adjugate_expansion := by
  intro K _ n A hn
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  have h := descending_expansion (D05.M05.adjugate (pencil A) i j) (n - 1)
    (adjugate_degree A hn i j)
  simpa only [show n - 1 + 1 = n by omega, Q, Matrix.map_apply, mul_comm] using h

private theorem pencil_matPoly (A : Matrix (Fin n) (Fin n) K) :
    matPolyEquiv (pencil A) = X + C A := by
  rw [pencil, map_add, matPolyEquiv_smul_one, matPolyEquiv_map_C]
  simp

/-- Reuse the independent formal differentiation prerequisite. -/
theorem determinant_derivative :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.determinant_derivative := by
  intro K _ n A
  cases n with
  | zero =>
    rw [D05.M05.DetDefinition.matrix_det_bridge,
      D05.M05.Adjugate.matrix_adjugate_bridge, Matrix.det_isEmpty]
    simp [Matrix.trace]
  | succ m =>
    simpa only [pencil, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using
      D05.M08.Coefficients.DeterminantDerivative.determinant_derivative
        (K := K) (n := m + 1) (by omega) A

private theorem Q_eq_coeff (A : Matrix (Fin n) (Fin n) K) (p : ℕ) :
    Q A p = (matPolyEquiv (D05.M05.adjugate (pencil A))).coeff (n - 1 - p) := by
  apply Matrix.ext
  intro i j
  simp [Q]

private theorem pencil_coeff_identity (A : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    (matPolyEquiv (D05.M05.adjugate (pencil A))).coeff k +
      A * (matPolyEquiv (D05.M05.adjugate (pencil A))).coeff (k + 1) =
      (D05.M05.determinant (pencil A)).coeff (k + 1) • 1 := by
  have h := congrArg (fun M => (matPolyEquiv M).coeff (k + 1))
    (D05.M05.Adjugate.mul_adjugate (pencil A))
  simpa only [map_mul, pencil_matPoly, add_mul, coeff_add, coeff_X_mul, coeff_C_mul,
    matPolyEquiv_smul_one, coeff_map, Algebra.algebraMap_eq_smul_one] using h

theorem initial_coefficient :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.initial_coefficient := by
  intro K _ n A hn
  have hz : (matPolyEquiv (D05.M05.adjugate (pencil A))).coeff n = 0 := by
    apply Matrix.ext
    intro i j
    simp only [matPolyEquiv_coeff_apply, Matrix.zero_apply]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (adjugate_degree A hn i j) (by omega))
  have h := pencil_coeff_identity A (n - 1)
  rw [show n - 1 + 1 = n by omega, hz, mul_zero, add_zero] at h
  rw [Q_eq_coeff, Nat.sub_zero]
  rw [show (D05.M05.determinant (pencil A)).coeff n = e A 0 by simp [e],
    leading_coefficient, one_smul] at h
  exact h

theorem coefficient_recurrence :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.coefficient_recurrence := by
  intro K _ n A p hp hpn
  rw [Q_eq_coeff, Q_eq_coeff]
  have h1 : n - 1 - p + 1 = n - p := by omega
  have h2 : n - 1 - (p - 1) = n - p := by omega
  simpa only [h1, h2, e] using pencil_coeff_identity A (n - 1 - p)

theorem trace_coefficient :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.trace_coefficient := by
  intro K _ n A p hp
  have h := congrArg (fun f : Polynomial K => f.coeff (n - 1 - p))
    (determinant_derivative A)
  have hk : n - 1 - p + 1 = n - p := by omega
  simp only [coeff_derivative, Matrix.trace, Polynomial.finsetSum_coeff] at h
  change (D05.M05.determinant (pencil A)).coeff (n - 1 - p + 1) *
    ((n - 1 - p : ℕ) + 1 : K) = Matrix.trace (Q A p) at h
  have hc : ((n - 1 - p : ℕ) : K) + 1 = ((n - p : ℕ) : K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ => (k : K)) hk
  rw [hk, hc] at h
  exact h.symm.trans (mul_comm _ _)

theorem coefficient_formula :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.coefficient_formula := by
  intro K _ n A p
  induction p with
  | zero =>
    intro hp
    rw [initial_coefficient A hp]
    simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_zero, pow_zero, one_mul]
    rw [leading_coefficient, one_smul]
  | succ p ih =>
    intro hp
    have hr := coefficient_recurrence A (p + 1) (by omega) hp
    simp only [Nat.add_sub_cancel] at hr
    have hs :
        ∑ j ∈ Finset.range (p + 1),
          ((-1 : K) ^ (j + 1) * e A (p + 1 - (j + 1))) • A ^ (j + 1) =
        -(A * Q A p) := by
      rw [ih (by omega), Matrix.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp [pow_succ', neg_smul]
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, pow_zero, one_mul]
    rw [hs]
    exact eq_neg_add_of_add_eq (by simpa only [add_comm] using hr)

private theorem constant_Q (A : Matrix (Fin n) (Fin n) K) :
    Q A (n - 1) = D05.M05.adjugate A := by
  unfold Q
  simp only [Nat.sub_self, coeff_zero_eq_eval_zero]
  rw [D05.M05.Adjugate.matrix_adjugate_bridge, D05.M05.Adjugate.matrix_adjugate_bridge]
  have hmap : (pencil A).map (Polynomial.eval (0 : K)) = A := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;> simp [pencil, hij]
  have h := (Polynomial.evalRingHom (0 : K)).map_adjugate (pencil A)
  simpa only [RingHom.mapMatrix_apply, Polynomial.coe_evalRingHom, hmap] using h

theorem constant_adjugate :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.constant_adjugate := by
  intro K _ n A hn
  have h := coefficient_formula A (n - 1) (by omega)
  rw [constant_Q, show n - 1 + 1 = n by omega] at h
  exact h

theorem sign_conversion :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.sign_conversion := by
  intro K _ n A
  have hm : (Polynomial.compRingHom (-X : Polynomial K)).mapMatrix (Matrix.charmatrix A) =
      (-1 : Polynomial K) • pencil A := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;>
      simp [Matrix.charmatrix, Matrix.scalar, pencil, hij, sub_eq_add_neg, add_comm]
  have hc : A.charpoly.comp (-X) = (-1 : Polynomial K) ^ n *
      D05.M05.determinant (pencil A) := by
    rw [D05.M05.DetDefinition.matrix_det_bridge, Matrix.charpoly,
      ← Polynomial.coe_compRingHom_apply, RingHom.map_det, hm, Matrix.det_smul, Fintype.card_fin]
  rw [hc]
  simp only [map_pow, map_neg, map_one]
  rw [← mul_assoc, ← mul_pow]
  simp

theorem characteristic_expansion :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.characteristic_expansion := by
  intro K _ n A
  have hc : A.charpoly = C ((-1 : K) ^ n) *
      (D05.M05.determinant (pencil A)).comp (-X) := by
    rw [sign_conversion, mul_comp, C_comp, comp_neg_X_comp_neg_X, ← mul_assoc, ← C_mul,
      ← mul_pow]
    simp
  rw [hc, determinant_expansion, sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hp
  have hs : (-1 : K) ^ n * (-1 : K) ^ (n - p) = (-1 : K) ^ p := by
    nth_rw 1 [show n = p + (n - p) by omega]
    rw [pow_add, mul_assoc, ← mul_pow]
    simp
  have hx (k : ℕ) : (-X : Polynomial K) ^ k = C ((-1 : K) ^ k) * X ^ k := by
    rw [neg_eq_neg_one_mul, mul_pow]
    simp only [map_pow, map_neg, map_one]
  simp only [mul_comp, C_comp, pow_comp, X_comp, hx, ← mul_assoc, ← C_mul]
  congr 2
  rw [mul_right_comm, hs]

theorem endomorphism_coefficients :
    Specs.D05.M08.Coefficients.AdjugateCoefficients.endomorphism_coefficients := by
  intro K V _ _ _ _ n b T
  dsimp only
  constructor
  · change LinearMap.charpoly T = _
    rw [← LinearMap.charpoly_toMatrix T b]
    exact characteristic_expansion (LinearMap.toMatrix b b T)
  · intro p hp
    rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.toMatrix_toLin]
    exact trace_coefficient _ p hp

end D05.M08.Coefficients.AdjugateCoefficients
