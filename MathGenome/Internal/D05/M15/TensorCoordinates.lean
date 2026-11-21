import MathGenome.Internal.D05.M04.ChangeBasis
import MathGenome.Internal.D05.M15.TensorBasis
import MathGenome.Internal.D05.M15.TensorMaps
import MathGenome.Internal.Specs.D05.M15.TensorCoordinates

/-! K05.15.tensor_coordinates: coordinates with finite support, independent
basis changes, Kronecker matrices in explicit product order, and the
trace/determinant supplement with its zero-factor qualifications. -/

namespace D05.M15.TensorCoordinates
open scoped TensorProduct Kronecker
open Matrix
open Specs.D05.M15.TensorCoordinates

noncomputable abbrev coefficients := @coefficients_value

theorem coefficient_tmul : Specs.D05.M15.TensorCoordinates.coefficient_tmul := by
  intro K V W I J _ _ _ _ _ e f v w i j
  simp only [coefficients_value, Module.Basis.tensorProduct_repr_tmul_apply,
    smul_eq_mul, mul_comm]

theorem general_map_entry : Specs.D05.M15.TensorCoordinates.general_map_entry := by
  intro K V W U Z I J I' J' _ _ _ _ _ _ _ _ _ e f u v S T k l i j
  rw [TensorProduct.map_tmul]
  exact coefficient_tmul u v (S (e i)) (T (f j)) k l

theorem reconstruction : Specs.D05.M15.TensorCoordinates.reconstruction := by
  intro K V W I J _ _ _ _ _ e f t
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, coefficients_value,
    Module.Basis.tensorProduct_apply', Prod.mk.eta] using
    (e.tensorProduct f).linearCombination_repr t

theorem basis_change_finsupp : Specs.D05.M15.TensorCoordinates.basis_change_finsupp := by
  intro K V W I J I' J' _ _ _ _ _ e f e' f' t i j
  have h := congrArg (fun z => (e.tensorProduct f).repr z (i,j)) (reconstruction e' f' t)
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul] at h
  simpa only [coefficients_value, mul_comm, mul_left_comm, mul_assoc] using h.symm

theorem finite_reconstruction : Specs.D05.M15.TensorCoordinates.finite_reconstruction := by
  intro K V W _ _ _ _ _ n m e f t
  simpa only [coefficients_value, Module.Basis.tensorProduct_apply', Fintype.sum_prod_type] using
    ((e.tensorProduct f).sum_repr t).symm

theorem kronecker_matrix : Specs.D05.M15.TensorCoordinates.kronecker_matrix := by
  intro K V W U Z _ _ _ _ _ _ _ _ _ n m r s e f u v S T
  exact TensorProduct.toMatrix_map e f u v S T

theorem kronecker_entry : Specs.D05.M15.TensorCoordinates.kronecker_entry := by
  intro K V W U Z _ _ _ _ _ _ _ _ _ n m r s e f u v S T k l i j
  rw [kronecker_matrix e f u v S T]
  rfl

theorem map_basis_expansion : Specs.D05.M15.TensorCoordinates.map_basis_expansion := by
  intro K V W U Z _ _ _ _ _ _ _ _ _ n m r s e f u v S T i j
  have h := finite_reconstruction u v (TensorProduct.map S T (e i ⊗ₜ[K] f j))
  simpa only [coefficients_value, TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply, LinearMap.toMatrix_apply, smul_eq_mul,
    mul_comm] using h

theorem map_coefficients : Specs.D05.M15.TensorCoordinates.map_coefficients := by
  intro K V W U Z _ _ _ _ _ _ _ _ _ n m r s e f u v S T t
  ext k l
  have h := LinearMap.toMatrix_mulVec_repr (e.tensorProduct f) (u.tensorProduct v)
    (TensorProduct.map S T) t
  have hk := congrFun h (k,l)
  rw [kronecker_matrix e f u v S T] at hk
  simp only [coefficients_value, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.mul_apply, Matrix.transpose_apply] at hk ⊢
  rw [← hk]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem basis_change_old : Specs.D05.M15.TensorCoordinates.basis_change_old := by
  intro K V W _ _ _ _ _ n m e e' f f' t
  have h := map_coefficients e' f' e f LinearMap.id LinearMap.id t
  simpa only [TensorProduct.map_id, LinearMap.id_apply,
    Specs.D05.M04.ChangeBasis.changeMatrix_value,
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value] using h

theorem basis_change_new : Specs.D05.M15.TensorCoordinates.basis_change_new := by
  intro K V W _ _ _ _ _ n m e e' f f' t
  rw [D05.M04.ChangeBasis.conversion_nonsingular_inverse,
    D05.M04.ChangeBasis.conversion_nonsingular_inverse]
  exact basis_change_old e' e f' f t

theorem lexicographic_entry : Specs.D05.M15.TensorCoordinates.lexicographic_entry := by
  intro K V W U Z _ _ _ _ _ _ _ _ _ n m r s e f u v S T k l i j
  simpa only [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply] using
    kronecker_entry e f u v S T k l i j

theorem basis_columns : Specs.D05.M15.TensorCoordinates.basis_columns := by
  intro K V _ _ _ n e e' a
  simpa only [Specs.D05.M04.ChangeBasis.changeMatrix_value,
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value, LinearMap.toMatrix_apply,
    LinearMap.id_apply] using (e.sum_repr (e' a)).symm

theorem trace_tensor : Specs.D05.M15.TensorCoordinates.trace_tensor := by
  intro K V W _ _ _ _ _ _ _ S T
  exact LinearMap.trace_tensorProduct' S T

theorem det_tensor : Specs.D05.M15.TensorCoordinates.det_tensor := by
  intro K V W _ _ _ _ _ _ _ S T
  classical
  let e := Module.finBasis K V
  let f := Module.finBasis K W
  rw [← LinearMap.det_toMatrix (e.tensorProduct f), TensorProduct.toMatrix_map,
    Matrix.det_kronecker, LinearMap.det_toMatrix, LinearMap.det_toMatrix]
  simp only [Fintype.card_fin]

theorem sandwich_tensor_bridge : Specs.D05.M15.TensorCoordinates.sandwich_tensor_bridge := by
  intro K V _ _ _ _ A B
  apply TensorProduct.ext'
  intro φ v
  ext x
  simp [sandwich, Module.End.mul_apply, LinearMap.dualMap_apply]

/-- Express the bridge as a conjugation of linear maps on the whole space. -/
private theorem sandwich_eq_conjugate {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (A B : Module.End K V) :
    sandwich A B = (dualTensorHomEquiv K V V).conj (TensorProduct.map B.dualMap A) := by
  let e := dualTensorHomEquiv K V V
  have h := sandwich_tensor_bridge A B
  have h' := congrArg (fun L => L.comp e.symm.toLinearMap) h
  dsimp only [e] at h'
  simpa only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap, LinearMap.comp_id, LinearEquiv.conj_apply] using h'

theorem trace_sandwich : Specs.D05.M15.TensorCoordinates.trace_sandwich := by
  intro K V _ _ _ _ A B
  rw [sandwich_eq_conjugate]
  rw [LinearMap.trace_conj' (R := K) (M := (Module.Dual K V) ⊗[K] V)
      (N := Module.End K V) (TensorProduct.map B.dualMap A) (dualTensorHomEquiv K V V),
    trace_tensor]
  simp only [LinearMap.dualMap_def, LinearMap.trace_transpose', mul_comm]

theorem det_sandwich : Specs.D05.M15.TensorCoordinates.det_sandwich := by
  intro K V _ _ _ _ A B
  rw [sandwich_eq_conjugate, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj (A := K) (M := (Module.Dual K V) ⊗[K] V)
      (N := Module.End K V) (TensorProduct.map B.dualMap A) (dualTensorHomEquiv K V V), det_tensor,
    LinearMap.det_dualMap, Subspace.dual_finrank_eq, ← mul_pow, mul_comm]

theorem injective_tensor : Specs.D05.M15.TensorCoordinates.injective_tensor := by
  intro K V W U Z _ _ _ _ _ _ _ _ _ S T hS hT
  have hleft : (TensorProduct.map S.leftInverse T.leftInverse).comp
      (TensorProduct.map S T) = LinearMap.id := by
    rw [← TensorProduct.map_comp, LinearMap.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr hS),
      LinearMap.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr hT), TensorProduct.map_id]
  intro x y h
  have := congrArg (TensorProduct.map S.leftInverse T.leftInverse) h
  simpa only [← LinearMap.comp_apply, hleft, LinearMap.id_apply] using this

/-- Nonzero vectors have a nonzero elementary tensor over a field. The
proof selects nonzero algebraic coordinates, without a dimension bound. -/
theorem tmul_ne_zero {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    v ⊗ₜ[K] w ≠ 0 := by
  classical
  let e := Module.Basis.ofVectorSpace K V
  let f := Module.Basis.ofVectorSpace K W
  have he : ∃ i, e.repr v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply e.repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using h i
  have hf : ∃ j, f.repr w j ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    apply f.repr.injective
    ext j
    simpa only [map_zero, Finsupp.zero_apply] using h j
  obtain ⟨i, hi⟩ := he
  obtain ⟨j, hj⟩ := hf
  intro h
  apply mul_ne_zero hi hj
  rw [← coefficient_tmul e f v w i j, h]
  simp only [coefficients_value, map_zero, Finsupp.zero_apply]

theorem injective_factors : Specs.D05.M15.TensorCoordinates.injective_factors := by
  intro K V W U Z _ _ _ _ _ _ _ _ _ _ _ S T h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  constructor
  · intro x y hxy
    by_contra hne
    apply tmul_ne_zero (K := K) (sub_ne_zero.mpr hne) hw
    apply h
    simp only [TensorProduct.map_tmul, map_sub, hxy, sub_self, TensorProduct.zero_tmul, map_zero]
  · intro x y hxy
    by_contra hne
    apply tmul_ne_zero (K := K) hv (sub_ne_zero.mpr hne)
    apply h
    simp only [TensorProduct.map_tmul, map_sub, hxy, sub_self, TensorProduct.tmul_zero, map_zero]

theorem invertible_factors : Specs.D05.M15.TensorCoordinates.invertible_factors := by
  intro K V W _ _ _ _ _ _ _ _ _ S T
  rw [Module.End.isUnit_iff, Module.End.isUnit_iff, Module.End.isUnit_iff]
  constructor
  · intro h
    obtain ⟨hS, hT⟩ := injective_factors S T h.1
    exact ⟨⟨hS, LinearMap.injective_iff_surjective.mp hS⟩,
      ⟨hT, LinearMap.injective_iff_surjective.mp hT⟩⟩
  · rintro ⟨hS, hT⟩
    exact TensorProduct.map_bijective hS hT

theorem zero_factor : Specs.D05.M15.TensorCoordinates.zero_factor := by
  intro K V W _ _ _ _ _ _ _ S T h
  have hsub : Subsingleton (V ⊗[K] W) := by
    rcases h with h | h
    · have := h
      infer_instance
    · have := h
      infer_instance
  have := hsub
  refine ⟨?_, ?_, LinearMap.det_eq_one_of_subsingleton _⟩
  · have h1 : TensorProduct.map S T = 1 := Subsingleton.elim _ _
    rw [h1]
    exact isUnit_one
  · have h0 : TensorProduct.map S T = 0 := Subsingleton.elim _ _
    rw [h0, map_zero]

end D05.M15.TensorCoordinates
