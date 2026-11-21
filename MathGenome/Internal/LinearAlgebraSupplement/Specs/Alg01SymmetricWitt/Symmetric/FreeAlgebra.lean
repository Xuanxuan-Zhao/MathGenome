import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Algebra

namespace Specs.Alg01SymmetricWitt.Symmetric.FreeAlgebra

universe u v w

open Specs.Alg01SymmetricWitt.Symmetric.Algebra (degree pureProduct)

/-- Every linear map into a commutative algebra has a unique algebra extension. -/
def existsUniqueExtension : Prop :=
  ∀ (R : Type u) (M : Type v) (A : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]
    (f : M →ₗ[R] A),
    ∃! F : SymmetricAlgebra R M →ₐ[R] A,
      F.toLinearMap.comp (SymmetricAlgebra.ι R M) = f

/-- An extension acts by the product formula in every degree and by the structure map on scalars. -/
def extensionValues : Prop :=
  ∀ (R : Type u) (M : Type v) (A : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]
    (f : M →ₗ[R] A) (F : SymmetricAlgebra R M →ₐ[R] A),
    F.toLinearMap.comp (SymmetricAlgebra.ι R M) = f →
      (∀ (n : ℕ) (x : Fin n → M),
        F ((pureProduct R M n x : degree R M n) : SymmetricAlgebra R M) = ∏ i, f (x i)) ∧
      ∀ r : R, F (algebraMap R (SymmetricAlgebra R M) r) = algebraMap R A r

end Specs.Alg01SymmetricWitt.Symmetric.FreeAlgebra
