import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Algebra
import Mathlib.RingTheory.TensorProduct.Basic

namespace Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra

open scoped TensorProduct
open Specs.Alg01SymmetricWitt.Symmetric.Algebra (pureProduct)

universe u v w

section

variable (R : Type u) (S : Type v) (M : Type w)
  [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]

/-- Extend the map on generators sending `x` to the symmetric class of `1 ⊗ x`. -/
noncomputable def comparisonHom :
    S ⊗[R] SymmetricAlgebra R M →ₐ[S] SymmetricAlgebra S (S ⊗[R] M) := by
  let liftTo (A : Type _) [CommRing A] [Algebra S A] (f : (S ⊗[R] M) →ₗ[S] A) :
      (S ⊗[R] SymmetricAlgebra R M) →ₐ[S] A := by
    letI : Algebra R A := Algebra.compHom A (algebraMap R S)
    letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
    exact AlgHom.liftEquiv R S (SymmetricAlgebra R M) A
      (SymmetricAlgebra.lift ((f.restrictScalars R).comp (TensorProduct.mk R S M 1)))
  exact liftTo _ (SymmetricAlgebra.ι S (S ⊗[R] M))

end

set_option linter.checkUnivs false in
def comparisonHomType :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    S ⊗[R] SymmetricAlgebra R M →ₐ[S] SymmetricAlgebra S (S ⊗[R] M)

/-- The canonical comparison is invertible, with the stated formulas on pure classes
and on the generators of its inverse. -/
def comparisonProperties : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    ∃ e : S ⊗[R] SymmetricAlgebra R M ≃ₐ[S] SymmetricAlgebra S (S ⊗[R] M),
      e.toAlgHom = comparisonHom R S M ∧
      (∀ (s : S) (x : M),
        e (s ⊗ₜ[R] SymmetricAlgebra.ι R M x) =
          s • SymmetricAlgebra.ι S (S ⊗[R] M) (1 ⊗ₜ[R] x)) ∧
      (∀ (n : ℕ) (s : S) (x : Fin n → M),
        e (s ⊗ₜ[R] (pureProduct R M n x : SymmetricAlgebra R M)) =
          s • (pureProduct S (S ⊗[R] M) n (fun i => 1 ⊗ₜ[R] x i) :
            SymmetricAlgebra S (S ⊗[R] M))) ∧
      e.symm.toLinearMap.comp (SymmetricAlgebra.ι S (S ⊗[R] M)) =
        (SymmetricAlgebra.ι R M).baseChange S

end Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra
