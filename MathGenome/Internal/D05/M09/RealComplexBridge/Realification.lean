import MathGenome.Internal.Specs.D05.M09.RealComplexBridge.Realification
import Mathlib.Basic.Complex.BigOperators
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

noncomputable section
open scoped BigOperators
namespace D05.M09.RealComplexBridge.Realification
open Specs.D05.M09.RealComplexBridge.Realification

private def grouping (n : ℕ) : (Fin 2 × Fin n) ≃ (Fin n ⊕ Fin n) where
  toFun p := if p.1 = 0 then .inl p.2 else .inr p.2
  invFun := Sum.elim (fun j => (0,j)) (fun j => (1,j))
  left_inv := by rintro ⟨i,j⟩; fin_cases i <;> simp
  right_inv := by intro j; cases j <;> simp

private def groupedBasis {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :=
  (Complex.basisOneI.smulTower b).reindex (grouping n)

private theorem basis_inl {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (j) :
    groupedBasis b (.inl j) = b j := by
  simp [groupedBasis, grouping, Module.Basis.smulTower_apply, Complex.coe_basisOneI]

private theorem basis_inr {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (j) :
    groupedBasis b (.inr j) = Complex.I • b j := by
  simp [groupedBasis, grouping, Module.Basis.smulTower_apply, Complex.coe_basisOneI]

private theorem repr_inl {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (v j) :
    (groupedBasis b).repr v (.inl j) = (b.repr v j).re := by
  simp [groupedBasis, grouping, Module.Basis.smulTower_repr, Complex.coe_basisOneI_repr]

private theorem repr_inr {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (v j) :
    (groupedBasis b).repr v (.inr j) = (b.repr v j).im := by
  simp [groupedBasis, grouping, Module.Basis.smulTower_repr, Complex.coe_basisOneI_repr]

theorem grouped_basis : Specs.D05.M09.RealComplexBridge.Realification.grouped_basis := by
  intro V _ _ n b
  refine ⟨groupedBasis b, basis_inl b, basis_inr b, repr_inl b, repr_inr b, ?_⟩
  intro T
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix_apply, basis_inl, basis_inr, repr_inl, repr_inr,
      realMatrix, map_smul, Finsupp.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im]

theorem real_dimension : Specs.D05.M09.RealComplexBridge.Realification.real_dimension := by
  intro V _ _ _
  simpa using (Module.finrank_mul_finrank ℝ ℂ V).symm

theorem determinant : Specs.D05.M09.RealComplexBridge.Realification.determinant := by
  intro V _ _ _ T
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem split_inverse : Specs.D05.M09.RealComplexBridge.Realification.split_inverse := by
  intro n
  constructor <;>
    simp only [splitMatrix, unsplitMatrix, Matrix.fromBlocks_multiply,
      Matrix.mul_smul, Matrix.mul_one, smul_smul] <;>
    ext i j <;> cases i <;> cases j <;>
    simp [Matrix.one_apply, Matrix.smul_apply, Complex.ext_iff] <;> split_ifs <;> norm_num

theorem split_coordinates : Specs.D05.M09.RealComplexBridge.Realification.split_coordinates := by
  intro n x y
  simp only [splitMatrix, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  cases i <;> simp [Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]

theorem unsplit_coordinates : Specs.D05.M09.RealComplexBridge.Realification.unsplit_coordinates := by
  intro n u v
  simp only [unsplitMatrix, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  cases i <;> simp [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul, Complex.inv_I] <;> ring

theorem intertwining : Specs.D05.M09.RealComplexBridge.Realification.intertwining := by
  intro n A
  simp only [splitMatrix, realMatrix, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    add_zero, zero_add]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.smul_apply, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

theorem matrix_charpoly : Specs.D05.M09.RealComplexBridge.Realification.matrix_charpoly := by
  intro n A
  let R := (realMatrix A).map (algebraMap ℝ ℂ)
  let D := Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ))
  have h := intertwining A
  change splitMatrix n * R = D * splitMatrix n at h
  have hconj : splitMatrix n * R * unsplitMatrix n = D := by
    rw [h, mul_assoc, (split_inverse n).1, mul_one]
  have hc : R.charpoly = D.charpoly := by
    rw [← hconj, Matrix.charpoly_mul_comm, ← mul_assoc, (split_inverse n).2, one_mul]
  rw [← Matrix.charpoly_map]
  change R.charpoly = _
  rw [hc]
  simp only [D, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_map]

theorem operator_charpoly : Specs.D05.M09.RealComplexBridge.Realification.operator_charpoly := by
  intro V _ _ _ T
  let b := Module.finBasis ℂ V
  obtain ⟨r, _, _, _, _, hr⟩ := grouped_basis b
  rw [← LinearMap.charpoly_toMatrix (T.restrictScalars ℝ) r, hr T, matrix_charpoly,
    LinearMap.charpoly_toMatrix T b]

theorem trace : Specs.D05.M09.RealComplexBridge.Realification.trace := by
  intro V _ _ _ T
  let b := Module.finBasis ℂ V
  obtain ⟨r, _, _, _, _, hr⟩ := grouped_basis b
  rw [LinearMap.trace_eq_matrix_trace ℝ r, hr T,
    LinearMap.trace_eq_matrix_trace ℂ b]
  simp [realMatrix, Matrix.trace, two_mul, Complex.re_sum]

theorem real_product : Specs.D05.M09.RealComplexBridge.Realification.real_product := by
  intro p
  have hc : (p.map (starRingEnd ℂ)).map (starRingEnd ℂ) = p := by
    ext k
    simp
  have hfix : (p * p.map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      p * p.map (starRingEnd ℂ) := by
    rw [Polynomial.map_mul, hc, mul_comm]
  refine ⟨hfix, ?_⟩
  let q := p * p.map (starRingEnd ℂ)
  refine ⟨Polynomial.ofFinsupp ⟨Finsupp.mapRange Complex.re (by simp) q.toFinsupp.coeff⟩, ?_⟩
  ext k
  have hk := congrArg (fun f : Polynomial ℂ => f.coeff k) hfix
  have hk' : (starRingEnd ℂ) (q.coeff k) = q.coeff k := by
    simpa only [Polynomial.coeff_map] using hk
  have him : (q.coeff k).im = 0 := by
    have hi := congrArg Complex.im hk'
    change -(q.coeff k).im = (q.coeff k).im at hi
    linarith
  simp only [Polynomial.coeff_map, Polynomial.coeff_ofFinsupp, Finsupp.mapRange_apply]
  change ((q.coeff k).re : ℂ) = q.coeff k
  apply Complex.ext <;> simp [him]

end D05.M09.RealComplexBridge.Realification
