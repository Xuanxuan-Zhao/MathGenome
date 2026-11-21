import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree
import Mathlib.RingTheory.TensorProduct.Maps

namespace Specs.Alg01SymmetricWitt.Symmetric.BaseChange

open scoped TensorProduct
open Specs.Alg01SymmetricWitt.Symmetric.Algebra (degree)
open Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra (comparisonHom)
open Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree
  (scalarExtensionGrading gradedComparison degreeComparison)

universe u v w m m'

section

variable {R : Type u} {M : Type m} {N : Type m'}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The symmetric algebra map induced by a linear map. -/
noncomputable def symMap (f : M →ₗ[R] N) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f)

/-- The degree map is the restriction of the induced symmetric algebra map. -/
def IsDegreeMap (n : ℕ) (f : M →ₗ[R] N) (g : degree R M n →ₗ[R] degree R N n) : Prop :=
  ∀ x, (g x : SymmetricAlgebra R N) = symMap f (x : SymmetricAlgebra R M)

end

section

variable (R : Type u) (S : Type v) (M : Type m)
  [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]

/-- The degreewise comparison is the restriction of the canonical algebra comparison
along the scalar extension of the degree inclusion. -/
def IsDegreeComparison (n : ℕ)
    (e : S ⊗[R] degree R M n ≃ₗ[S] degree S (S ⊗[R] M) n) : Prop :=
  ∀ z, (e z : SymmetricAlgebra S (S ⊗[R] M)) =
    comparisonHom R S M ((degree R M n).subtype.baseChange S z)

end

/-- The canonical comparison is a graded algebra isomorphism with the stated values on
pure classes, and induces the specified linear isomorphism in every degree. -/
def canonicalComparisons : Prop :=
  BaseChangeAlgebra.comparisonProperties.{u, v, m} ∧ scalarExtensionGrading.{u, v, m} ∧
    gradedComparison.{u, v, m} ∧ degreeComparison.{u, v, m}

/-- The canonical algebra comparison is natural for every linear map. -/
def algebraNaturality : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type m) (N : Type m')
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
    (symMap (f.baseChange S)).comp (comparisonHom R S M) =
      (comparisonHom R S N).comp (Algebra.TensorProduct.map (AlgHom.id S S) (symMap f))

/-- The naturality square in degree `n`, with horizontal maps induced by scalar
extension and vertical maps induced by `f`. -/
def degreeNaturality : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type m) (N : Type m')
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (n : ℕ),
    ∃ (g : degree R M n →ₗ[R] degree R N n)
      (gS : degree S (S ⊗[R] M) n →ₗ[S] degree S (S ⊗[R] N) n)
      (e : S ⊗[R] degree R M n ≃ₗ[S] degree S (S ⊗[R] M) n)
      (e' : S ⊗[R] degree R N n ≃ₗ[S] degree S (S ⊗[R] N) n),
      IsDegreeMap n f g ∧ IsDegreeMap n (f.baseChange S) gS ∧
      IsDegreeComparison R S M n e ∧ IsDegreeComparison R S N n e' ∧
      gS.comp e.toLinearMap = e'.toLinearMap.comp (g.baseChange S)

/-- Direct scalar extension agrees with successive scalar extensions after reassociating
the algebra on the source and the generating module on the target. -/
def algebraComposition : Prop :=
  ∀ (R : Type u) (S : Type v) (U : Type w) (M : Type m)
    [CommRing R] [CommRing S] [CommRing U] [Algebra R S] [Algebra S U]
    [AddCommGroup M] [Module R M],
    letI : Algebra R U := Algebra.compHom U (algebraMap R S)
    letI : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' rfl
    comparisonHom R U M =
      (symMap (TensorProduct.AlgebraTensorModule.cancelBaseChange R S U U M).toLinearMap).comp
        ((comparisonHom S U (S ⊗[R] M)).comp
          ((Algebra.TensorProduct.map (AlgHom.id U U) (comparisonHom R S M)).comp
            (Algebra.TensorProduct.cancelBaseChange R S U U (SymmetricAlgebra R M)).symm.toAlgHom))

/-- The same reassociation identity on each homogeneous degree. -/
def degreeComposition : Prop :=
  ∀ (R : Type u) (S : Type v) (U : Type w) (M : Type m)
    [CommRing R] [CommRing S] [CommRing U] [Algebra R S] [Algebra S U]
    [AddCommGroup M] [Module R M] (n : ℕ),
    letI : Algebra R U := Algebra.compHom U (algebraMap R S)
    letI : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' rfl
    ∃ (g : degree U (U ⊗[S] (S ⊗[R] M)) n →ₗ[U] degree U (U ⊗[R] M) n)
      (eRS : S ⊗[R] degree R M n ≃ₗ[S] degree S (S ⊗[R] M) n)
      (eSU : U ⊗[S] degree S (S ⊗[R] M) n ≃ₗ[U] degree U (U ⊗[S] (S ⊗[R] M)) n)
      (eRU : U ⊗[R] degree R M n ≃ₗ[U] degree U (U ⊗[R] M) n),
      IsDegreeMap n (TensorProduct.AlgebraTensorModule.cancelBaseChange R S U U M).toLinearMap g ∧
      IsDegreeComparison R S M n eRS ∧ IsDegreeComparison S U (S ⊗[R] M) n eSU ∧
      IsDegreeComparison R U M n eRU ∧
      eRU.toLinearMap =
        g.comp (eSU.toLinearMap.comp ((eRS.toLinearMap.baseChange U).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S U U
            (degree R M n)).symm.toLinearMap))

end Specs.Alg01SymmetricWitt.Symmetric.BaseChange
