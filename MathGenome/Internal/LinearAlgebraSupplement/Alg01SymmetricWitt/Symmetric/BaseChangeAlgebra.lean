import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.FreeAlgebra

namespace Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra

open scoped TensorProduct
open Alg01SymmetricWitt.Symmetric.Algebra (pureProduct pureProductCoe)

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

noncomputable abbrev comparisonHom :=
  Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra.comparisonHom R S M

@[simp]
theorem comparisonHom_tmul_ι (s : S) (x : M) :
    comparisonHom R S M (s ⊗ₜ[R] SymmetricAlgebra.ι R M x) =
      s • SymmetricAlgebra.ι S (S ⊗[R] M) (1 ⊗ₜ[R] x) := by
  simp [comparisonHom, Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra.comparisonHom]

private noncomputable def inverseHom :
    SymmetricAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] SymmetricAlgebra R M :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).baseChange S)

private theorem inverseHom_comp_comparisonHom :
    (inverseHom R S M).comp (comparisonHom R S M) = AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext_ring
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change inverseHom R S M
    (comparisonHom R S M (1 ⊗ₜ[R] SymmetricAlgebra.ι R M x)) = _
  simp [inverseHom]

private theorem comparisonHom_comp_inverseHom :
    (comparisonHom R S M).comp (inverseHom R S M) = AlgHom.id S _ := by
  apply SymmetricAlgebra.algHom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  change comparisonHom R S M
    (inverseHom R S M (SymmetricAlgebra.ι S (S ⊗[R] M) (s ⊗ₜ[R] x))) =
      SymmetricAlgebra.ι S (S ⊗[R] M) (s ⊗ₜ[R] x)
  rw [inverseHom, SymmetricAlgebra.lift_ι_apply, LinearMap.baseChange_tmul, comparisonHom_tmul_ι]
  rw [← map_smul, ← TensorProduct.tmul_eq_smul_one_tmul]

/-- The canonical symmetric-algebra comparison for extension of scalars. -/
noncomputable def comparison :
    S ⊗[R] SymmetricAlgebra R M ≃ₐ[S] SymmetricAlgebra S (S ⊗[R] M) :=
  AlgEquiv.ofAlgHom (comparisonHom R S M) (inverseHom R S M)
    (comparisonHom_comp_inverseHom R S M) (inverseHom_comp_comparisonHom R S M)

@[simp]
theorem comparison_toAlgHom : (comparison R S M).toAlgHom = comparisonHom R S M :=
  rfl

@[simp]
theorem comparison_tmul_ι (s : S) (x : M) :
    comparison R S M (s ⊗ₜ[R] SymmetricAlgebra.ι R M x) =
      s • SymmetricAlgebra.ι S (S ⊗[R] M) (1 ⊗ₜ[R] x) :=
  comparisonHom_tmul_ι R S M s x

@[simp]
theorem comparison_symm_comp_ι :
    (comparison R S M).symm.toLinearMap.comp (SymmetricAlgebra.ι S (S ⊗[R] M)) =
      (SymmetricAlgebra.ι R M).baseChange S :=
  SymmetricAlgebra.lift_comp_ι _

theorem comparison_tmul_pureProduct (n : ℕ) (s : S) (x : Fin n → M) :
    comparison R S M (s ⊗ₜ[R] (pureProduct R M n x : SymmetricAlgebra R M)) =
      s • (pureProduct S (S ⊗[R] M) n (fun i => 1 ⊗ₜ[R] x i) :
        SymmetricAlgebra S (S ⊗[R] M)) := by
  simp only [pureProductCoe]
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
  change s • comparison R S M
    (Algebra.TensorProduct.includeRight (A := S) (∏ i, SymmetricAlgebra.ι R M (x i))) = _
  rw [map_prod, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    rw [Algebra.TensorProduct.includeRight_apply, comparison_tmul_ι, one_smul]

theorem comparisonProperties :
    Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra.comparisonProperties :=
  fun R S M _ _ _ _ _ =>
    ⟨comparison R S M, comparison_toAlgHom R S M, comparison_tmul_ι R S M,
      comparison_tmul_pureProduct R S M, comparison_symm_comp_ι R S M⟩

end Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra
