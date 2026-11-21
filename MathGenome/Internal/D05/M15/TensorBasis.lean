import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M03.BasisExtension
import MathGenome.Internal.D05.M15.TensorUniversal
import MathGenome.Internal.D05.M15.TensorExistence
import MathGenome.Internal.Specs.D05.M15.TensorBasis

/-! K05.15.tensor_basis: the product basis for algebraic tensor products.
Mathlib constructs its basis via finite-support coordinate equivalences;
`tensorProduct_apply` identifies its vectors with the paper's elementary
ones. Thus no dimension or nonzero-factor assumption enters the basis proof.
-/
namespace D05.M15.TensorBasis

open scoped TensorProduct

theorem tensor_basis : Specs.D05.M15.TensorBasis.tensor_basis := by
  intro K V W I J _ _ _ _ _ e f
  exact ⟨e.tensorProduct f, fun p => e.tensorProduct_apply' f p⟩

theorem independent_and_span : Specs.D05.M15.TensorBasis.independent_and_span := by
  intro K V W I J _ _ _ _ _ e f
  exact (D05.M02.Basis.basis_iff_independent_span _).mp (tensor_basis e f)

theorem unique_expansion : Specs.D05.M15.TensorBasis.unique_expansion := by
  intro K V W I J _ _ _ _ _ e f z
  exact (D05.M02.Basis.basis_iff_unique_expansion _).mp (tensor_basis e f) z

/-- The product basis coordinate is the linearization of the product of
factor coordinates. Applying it to a finite linear combination recovers
its coefficient, which is the coefficient-extraction argument in the paper. -/
theorem coordinate_functionals : Specs.D05.M15.TensorBasis.coordinate_functionals := by
  intro K V W I J _ _ _ _ _ e f i j
  refine ⟨(e.tensorProduct f).coord (i, j), ?_, ?_⟩
  · intro v w
    simp only [Module.Basis.coord_apply, Module.Basis.tensorProduct_repr_tmul_apply,
      smul_eq_mul, mul_comm]
  · intro a
    change (e.tensorProduct f).repr
      (Finsupp.linearCombination K (fun p : I × J => e p.1 ⊗ₜ[K] f p.2) a) (i, j) = _
    have hfam : (fun p : I × J => e p.1 ⊗ₜ[K] f p.2) = e.tensorProduct f := by
      funext p
      exact (e.tensorProduct_apply' f p).symm
    rw [hfam, Module.Basis.repr_linearCombination]

theorem finite_dimension : Specs.D05.M15.TensorBasis.finite_dimension := by
  intro K V W _ _ _ _ _ _ _
  classical
  let e := Module.finBasis K V
  let f := Module.finBasis K W
  exact ⟨(e.tensorProduct f).finiteDimensional_of_finite,
    Module.finrank_tensorProduct⟩

theorem zero_left : Specs.D05.M15.TensorBasis.zero_left := by
  intro K V W _ _ _ _ _ _ z
  exact Subsingleton.elim z 0

theorem zero_right : Specs.D05.M15.TensorBasis.zero_right := by
  intro K V W _ _ _ _ _ _ z
  exact Subsingleton.elim z 0

end D05.M15.TensorBasis
