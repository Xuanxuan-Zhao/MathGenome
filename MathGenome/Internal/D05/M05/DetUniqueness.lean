import MathGenome.Internal.Specs.D05.M05.DetUniqueness
import MathGenome.Internal.D05.M05.DetDefinition
import MathGenome.Internal.D05.M05.Alternating
import Mathlib.LinearAlgebra.Determinant

/-! K05.05.det_uniqueness: normalized column forms over commutative rings. -/

namespace D05.M05.DetUniqueness

theorem general_formula : D05.Specs.DetUniqueness.general_formula := by
  intro R _ n f v
  have h := congrArg
    (fun g : AlternatingMap R (Fin n → R) R (Fin n) => g v)
    (f.eq_smul_basis_det (Pi.basisFun R (Fin n)))
  rw [smul_apply, Pi.basisFun_det_apply, smul_eq_mul] at h
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  change f v = f (fun j i => (1 : Matrix (Fin n) (Fin n) R) i j) *
    Matrix.det (Matrix.transpose (Matrix.of v))
  rw [Matrix.det_transpose]
  have hb : (fun j i => (1 : Matrix (Fin n) (Fin n) R) i j) =
      (fun j => Pi.basisFun R (Fin n) j) := by
    funext j i
    simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  simpa only [hb] using h

theorem multilinear_formula : D05.Specs.DetUniqueness.multilinear_formula := by
  intro R _ n f hf v
  obtain ⟨a, ha⟩ := D05.M05.Alternating.alternating_iff_bundled f |>.mp hf
  rw [← ha]
  exact general_formula a v

theorem normalized_unique : D05.Specs.DetUniqueness.normalized_unique := by
  intro R _ n
  obtain ⟨f, hf, hnorm⟩ := D05.M05.DetDefinition.normalized_column_form R n
  refine ⟨f, hf, hnorm, ?_⟩
  intro g hg
  apply AlternatingMap.ext
  intro v
  rw [general_formula g v, hg, one_mul, hf]

theorem empty_case : D05.Specs.DetUniqueness.empty_case := by
  intro R _ f v
  exact ⟨congrArg f (Subsingleton.elim _ _),
    D05.M05.DetDefinition.empty_determinant _⟩

end D05.M05.DetUniqueness
