import MathGenome.Internal.Specs.D05.M11.Pfaffian.Congruence
import MathGenome.Internal.D05.M11.Pfaffian
import MathGenome.Internal.D05.M15.DeterminantLine
import MathGenome.Internal.D05.M07.DualMap

noncomputable section
namespace D05.M11.Pfaffian.Congruence

open scoped BigOperators
open Specs.D05.M11.Pfaffian

/-- The dual matrix is the ordinary transpose, with no inverse involved. -/
lemma dual_coordinate (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (coordinateBasis n).repr ((Matrix.toLin' P).dualMap (coordinateBasis n i)) j =
      P i j := by
  simp [coordinateBasis, Module.Basis.dualBasis_repr, LinearMap.dualMap_apply,
    Matrix.toLin'_apply, Pi.basisFun_apply]

lemma dual_coordinate_expansion (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (Matrix.toLin' P).dualMap (coordinateBasis n i) =
      ∑ j, P i j • coordinateBasis n j := by
  rw [← (coordinateBasis n).sum_repr ((Matrix.toLin' P).dualMap (coordinateBasis n i))]
  simp_rw [dual_coordinate]

/-- Congruence preserves skew symmetry even when the coordinate map is singular. -/
lemma congruence_skew (m : ℕ) (A P : Matrix (Fin (2*m)) (Fin (2*m)) ℝ)
    (hA : ∀ i j, A i j = -A j i) :
    ∀ i j, (P.transpose * A * P) i j = -(P.transpose * A * P) j i := by
  have ht : A.transpose = -A := by
    ext i j
    exact hA j i
  have h : (P.transpose * A * P).transpose = -(P.transpose * A * P) := by
    simp [Matrix.transpose_mul, ht, Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun h j) i

/-- Change of coefficients in the full ordered-pair expression for a two-form. -/
lemma full_pair_pullback (m : ℕ) (A P : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) :
    ExteriorAlgebra.map (Matrix.toLin' P).dualMap
      (∑ i, ∑ j, A i j •
        (ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) i) *
         ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) j))) =
    ∑ k, ∑ l, (P.transpose * A * P) k l •
        (ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) k) *
         ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) l)) := by
  classical
  simp only [map_sum, map_smul, map_mul, ExteriorAlgebra.map_apply_ι,
    dual_coordinate_expansion, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_smul]
  simp_rw [Finset.smul_sum, smul_smul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
    arg 2
    ext l
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext l
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

theorem pullback_omega : Specs.D05.M11.Pfaffian.Congruence.pullback_omega := by
  intro m A P hA
  have h := full_pair_pullback m A P
  rw [D05.M11.Pfaffian.full_pair_sum_eq_two_omega m A hA,
    D05.M11.Pfaffian.full_pair_sum_eq_two_omega m _ (congruence_skew m A P hA),
    map_smul] at h
  exact (smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) h

theorem pullback_volume : Specs.D05.M11.Pfaffian.Congruence.pullback_volume := by
  intro m P
  rw [volume_value, ExteriorAlgebra.map_apply_ιMulti]
  have h := D05.M15.DeterminantLine.wedge_expansion (coordinateBasis (2*m))
    ((Matrix.toLin' P).dualMap ∘ coordinateBasis (2*m))
  have hm : Matrix.of (fun i j => (coordinateBasis (2*m)).repr
      (((Matrix.toLin' P).dualMap ∘ coordinateBasis (2*m)) j) i) = P.transpose := by
    ext i j
    exact dual_coordinate (2*m) P j i
  rw [hm, D05.M05.DetDefinition.matrix_det_bridge, Matrix.det_transpose,
    ← D05.M05.DetDefinition.matrix_det_bridge] at h
  exact congrArg (fun z : ⋀[ℝ]^(2*m) (Covectors (2*m)) =>
    (z : ExteriorAlgebra ℝ (Covectors (2*m)))) h

theorem congruence : Specs.D05.M11.Pfaffian.Congruence.congruence := by
  intro m A P hA
  have h := congrArg (ExteriorAlgebra.map (Matrix.toLin' P).dualMap)
    (D05.M11.Pfaffian.wedge_normalization m A hA)
  rw [map_smul, map_pow, pullback_omega m A P hA, map_smul, pullback_volume m P,
    D05.M11.Pfaffian.wedge_normalization m _ (congruence_skew m A P hA),
    smul_smul, mul_comm (pfaffian_value A)] at h
  exact smul_left_injective ℝ (D05.M11.Pfaffian.volume_ne_zero m) h

theorem empty_congruence : Specs.D05.M11.Pfaffian.Congruence.empty_congruence := by
  intro A P
  rw [D05.M11.Pfaffian.empty_pfaffian A, D05.M11.Pfaffian.empty_pfaffian,
    D05.M05.DetDefinition.empty_determinant P, mul_one]
  exact ⟨rfl, rfl⟩

end D05.M11.Pfaffian.Congruence
