import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.BaseChange
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.BaseChangeDegree

namespace Alg01SymmetricWitt.Symmetric.BaseChange

open scoped TensorProduct
open Alg01SymmetricWitt.Symmetric.Algebra (degree degreeMap pureProduct pureProductCoe)
open Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra
  (comparisonHom comparisonHom_tmul_ι comparisonProperties)
open Alg01SymmetricWitt.Symmetric.BaseChangeDegree
  (scalarExtensionGrading gradedComparison degreeComparison degreeEquiv degreeEquiv_coe
    degreeEquiv_tmul_pureProduct degreeBaseChange_ext)
open Specs.Alg01SymmetricWitt.Symmetric.BaseChange (symMap IsDegreeMap IsDegreeComparison)

universe u v m

theorem canonicalComparisons :
    Specs.Alg01SymmetricWitt.Symmetric.BaseChange.canonicalComparisons.{u, v, m} :=
  ⟨comparisonProperties, scalarExtensionGrading, gradedComparison, degreeComparison⟩

section InducedMaps

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

@[simp]
theorem symMap_ι (f : M →ₗ[R] N) (x : M) :
    symMap f (SymmetricAlgebra.ι R M x) = SymmetricAlgebra.ι R N (f x) :=
  SymmetricAlgebra.lift_ι_apply _ _

private theorem symMap_pureProduct (f : M →ₗ[R] N) (n : ℕ) (x : Fin n → M) :
    symMap f (pureProduct R M n x : SymmetricAlgebra R M) =
      (pureProduct R N n (fun i ↦ f (x i)) : SymmetricAlgebra R N) := by
  simp only [pureProductCoe, map_prod, symMap_ι]

private theorem symMap_comp_degreeMap (f : M →ₗ[R] N) (n : ℕ) :
    (symMap f).toLinearMap.comp (degreeMap R M n) =
      (degreeMap R N n).comp (PiTensorProduct.map (fun _ : Fin n ↦ f)) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod]
  exact symMap_pureProduct f n x

/-- A linear map induces a linear map on the homogeneous symmetric degree. -/
noncomputable def mapDegree (f : M →ₗ[R] N) (n : ℕ) :
    degree R M n →ₗ[R] degree R N n :=
  ((symMap f).toLinearMap.comp (degree R M n).subtype).codRestrict (degree R N n) <| by
    rintro ⟨_, t, rfl⟩
    exact ⟨_, (LinearMap.congr_fun (symMap_comp_degreeMap f n) t).symm⟩

theorem mapDegree_coe (f : M →ₗ[R] N) (n : ℕ) : IsDegreeMap n f (mapDegree f n) :=
  fun _ ↦ rfl

@[simp]
theorem mapDegree_pureProduct (f : M →ₗ[R] N) (n : ℕ) (x : Fin n → M) :
    mapDegree f n (pureProduct R M n x) = pureProduct R N n (fun i ↦ f (x i)) :=
  Subtype.ext (symMap_pureProduct f n x)

end InducedMaps

theorem algebraNaturality : Specs.Alg01SymmetricWitt.Symmetric.BaseChange.algebraNaturality := by
  intro R S M N _ _ _ _ _ _ _ f
  apply Algebra.TensorProduct.ext_ring
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change symMap (f.baseChange S) (comparisonHom R S M (1 ⊗ₜ[R] SymmetricAlgebra.ι R M x)) =
    comparisonHom R S N
      (Algebra.TensorProduct.map (AlgHom.id S S) (symMap f) (1 ⊗ₜ[R] SymmetricAlgebra.ι R M x))
  simp

section Naturality

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem degreeEquiv_natural (f : M →ₗ[R] N) (n : ℕ) :
    (mapDegree (f.baseChange S) n).comp (degreeEquiv R S M n).toLinearMap =
      (degreeEquiv R S N n).toLinearMap.comp ((mapDegree f n).baseChange S) := by
  apply degreeBaseChange_ext R S M
  intro s x
  simp [degreeEquiv_tmul_pureProduct]

end Naturality

theorem degreeNaturality : Specs.Alg01SymmetricWitt.Symmetric.BaseChange.degreeNaturality := by
  intro R S M N _ _ _ _ _ _ _ f n
  exact ⟨mapDegree f n, mapDegree (f.baseChange S) n, degreeEquiv R S M n, degreeEquiv R S N n,
    mapDegree_coe f n, mapDegree_coe (f.baseChange S) n, degreeEquiv_coe R S M n,
    degreeEquiv_coe R S N n, degreeEquiv_natural f n⟩

theorem algebraComposition : Specs.Alg01SymmetricWitt.Symmetric.BaseChange.algebraComposition := by
  intro R S U M _ _ _ _ _ _ _
  let : Algebra R U := Algebra.compHom U (algebraMap R S)
  let : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' rfl
  apply Algebra.TensorProduct.ext_ring
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change comparisonHom R U M (1 ⊗ₜ[R] SymmetricAlgebra.ι R M x) =
    symMap (TensorProduct.AlgebraTensorModule.cancelBaseChange R S U U M).toLinearMap
      (comparisonHom S U (S ⊗[R] M)
        (Algebra.TensorProduct.map (AlgHom.id U U) (comparisonHom R S M)
          ((Algebra.TensorProduct.cancelBaseChange R S U U (SymmetricAlgebra R M)).symm
            (1 ⊗ₜ[R] SymmetricAlgebra.ι R M x))))
  simp

section Composition

variable (R S U M : Type*) [CommRing R] [CommRing S] [CommRing U]
  [Algebra R S] [Algebra S U] [Algebra R U] [IsScalarTower R S U]
  [AddCommGroup M] [Module R M]

theorem degreeEquiv_comp (n : ℕ) :
    (degreeEquiv R U M n).toLinearMap =
      (mapDegree (TensorProduct.AlgebraTensorModule.cancelBaseChange R S U U M).toLinearMap
        n).comp ((degreeEquiv S U (S ⊗[R] M) n).toLinearMap.comp
          (((degreeEquiv R S M n).toLinearMap.baseChange U).comp
            (TensorProduct.AlgebraTensorModule.cancelBaseChange R S U U
              (degree R M n)).symm.toLinearMap)) := by
  apply degreeBaseChange_ext R U M
  intro s x
  simp [degreeEquiv_tmul_pureProduct]

end Composition

theorem degreeComposition : Specs.Alg01SymmetricWitt.Symmetric.BaseChange.degreeComposition := by
  intro R S U M _ _ _ _ _ _ _ n
  let : Algebra R U := Algebra.compHom U (algebraMap R S)
  let : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' rfl
  let f := (TensorProduct.AlgebraTensorModule.cancelBaseChange R S U U M).toLinearMap
  exact ⟨mapDegree f n, degreeEquiv R S M n, degreeEquiv S U (S ⊗[R] M) n,
    degreeEquiv R U M n, mapDegree_coe f n, degreeEquiv_coe R S M n,
    degreeEquiv_coe S U (S ⊗[R] M) n, degreeEquiv_coe R U M n, degreeEquiv_comp R S U M n⟩

end Alg01SymmetricWitt.Symmetric.BaseChange
