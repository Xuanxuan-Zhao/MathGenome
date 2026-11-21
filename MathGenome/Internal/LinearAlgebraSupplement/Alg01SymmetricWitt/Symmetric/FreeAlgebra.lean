import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.Algebra

namespace Alg01SymmetricWitt.Symmetric.FreeAlgebra

open Alg01SymmetricWitt.Symmetric.Algebra (degree pureProduct pureProductCoe)

variable (R M A : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A]

/-- Every linear map into a commutative algebra has a unique algebra extension. -/
theorem existsUniqueExtension (f : M →ₗ[R] A) :
    ∃! F : SymmetricAlgebra R M →ₐ[R] A,
      F.toLinearMap.comp (SymmetricAlgebra.ι R M) = f := by
  refine ⟨SymmetricAlgebra.lift f, SymmetricAlgebra.lift_comp_ι f, ?_⟩
  intro F hF
  exact SymmetricAlgebra.algHom_ext (hF.trans (SymmetricAlgebra.lift_comp_ι f).symm)

/-- An extension acts by the product formula in every degree and by the structure map on scalars. -/
theorem extensionValues (f : M →ₗ[R] A) (F : SymmetricAlgebra R M →ₐ[R] A)
    (hF : F.toLinearMap.comp (SymmetricAlgebra.ι R M) = f) :
    (∀ (n : ℕ) (x : Fin n → M),
      F ((pureProduct R M n x : degree R M n) : SymmetricAlgebra R M) = ∏ i, f (x i)) ∧
    ∀ r : R, F (algebraMap R (SymmetricAlgebra R M) r) = algebraMap R A r := by
  refine ⟨?_, F.commutes⟩
  intro n x
  rw [pureProductCoe, map_prod]
  exact Finset.prod_congr rfl fun i _ => DFunLike.congr_fun hF (x i)

end Alg01SymmetricWitt.Symmetric.FreeAlgebra
