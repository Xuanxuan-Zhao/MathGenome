import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.KillingCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SemisimpleBaseChange

/-! LA-U04: scalar extension preserves semisimplicity.
The Killing matrix in the scalar-extended basis is obtained by applying
the field embedding entrywise. Its determinant stays nonzero, including
for the empty basis of the zero Lie algebra. -/

universe u v w t
open scoped TensorProduct

namespace LieAlgebrasAndRepresentations

section BilinearForms

variable {k : Type u} {K : Type v} {V : Type w}
  [Field k] [Field K] [Algebra k K] [AddCommGroup V] [Module k V]

/-- Scalar extension applies the field embedding to each Gram matrix entry. -/
theorem bilinForm_baseChange_matrix {ι : Type t} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (B : LinearMap.BilinForm k V) :
    LinearMap.BilinForm.toMatrix (b.baseChange K) (B.baseChange K) =
      (LinearMap.BilinForm.toMatrix b B).map (algebraMap k K) := by
  ext i j
  simp [Algebra.algebraMap_eq_smul_one]

/-- A nondegenerate form on a finite-dimensional vector space stays
nondegenerate over any extension field. -/
theorem bilinForm_nondegenerate_baseChange [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate) :
    (B.baseChange K).Nondegenerate := by
  classical
  let b := Module.finBasis k V
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange K)).mpr
  rw [bilinForm_baseChange_matrix, ← (algebraMap k K).mapMatrix_apply,
    ← RingHom.map_det]
  exact (map_ne_zero (algebraMap k K)).mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB)

end BilinearForms

variable (k : Type u) (K : Type v) (L : Type w)
  [Field k] [Field K] [Algebra k K]
  [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

/-- The Killing form commutes with extension of scalars. -/
theorem killingForm_baseChange :
    killingForm K (K ⊗[k] L) = (killingForm k L).baseChange K :=
  LieModule.traceForm_baseChange k L L K

/-- The Killing matrix is the same matrix over the extension field. -/
theorem killingForm_baseChange_matrix {ι : Type t} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k L) :
    LinearMap.BilinForm.toMatrix (b.baseChange K) (killingForm K (K ⊗[k] L)) =
      (LinearMap.BilinForm.toMatrix b (killingForm k L)).map (algebraMap k K) := by
  rw [killingForm_baseChange]
  exact bilinForm_baseChange_matrix b (killingForm k L)

/-- Scalar extension of a finite-dimensional semisimple Lie algebra in
characteristic zero is semisimple, with the radical definition of LA-B05. -/
theorem lieAlgebra_semisimple_baseChange [CharZero k] (h : IsSemisimple k L) :
    IsSemisimple K (K ⊗[k] L) := by
  have : CharZero K := Algebra.charZero_of_charZero k K
  apply (semisimple_iff_killingForm_nondegenerate K (K ⊗[k] L)).mpr
  rw [killingForm_baseChange]
  exact bilinForm_nondegenerate_baseChange (killingForm k L)
    ((semisimple_iff_killingForm_nondegenerate k L).mp h)

/-- In particular, complexification preserves semisimplicity of real Lie algebras. -/
theorem semisimple_complexification (L : Type w)
    [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (h : IsSemisimple ℝ L) : IsSemisimple ℂ (ℂ ⊗[ℝ] L) :=
  lieAlgebra_semisimple_baseChange ℝ ℂ L h

end LieAlgebrasAndRepresentations
