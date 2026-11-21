import MathGenome.Internal.Specs.D07.Ch22.TensorDirectSums
import MathGenome.Internal.D07.Ch22.FreeDirectSums
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
K07.22.tensor_direct_sums. The arbitrary-index equivalence is Mathlib's
`directSumLeft`; its coordinates, inverse extension, and finite-sum rule
are specified explicitly. Finite presentations use finite function spaces,
with the product index transported to `Fin (a*b)`. Intrinsic ranks are
asserted only over nonzero rings. The invariant basis number instance used
below is proved in Mathlib by passing to a maximal-ideal quotient field.
-/

noncomputable section
universe u v w t
namespace D07.Ch22.TensorDirectSums
open Specs.D07.Ch22.TensorDirectSums
open scoped TensorProduct BigOperators

theorem distribution : Distribution.{u, v, w, t} := by
  classical
  intro R _ E M _ _ N _ _
  refine ⟨TensorProduct.directSumLeft R R M N, ⟨?_, ?_⟩, ?_⟩
  · exact TensorProduct.directSumLeft_tmul R R
  · exact TensorProduct.directSumLeft_symm_lof_tmul R R
  · intro e he
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro m n
    apply DirectSum.ext
    intro i
    exact (he.1 m n i).trans (TensorProduct.directSumLeft_tmul R R m n i).symm

theorem forwardCoordinates : ForwardCoordinates.{u, v, w, t} := by
  classical
  intro R _ E M _ _ N _ _ m n i
  exact TensorProduct.directSumLeft_tmul R R m n i

theorem finiteSupport : FiniteSupport.{u, v, w, t} := by
  classical
  intro R _ E M _ _ N _ _ m n i hi
  by_contra hm
  have hz : m i = 0 := DFinsupp.notMem_support_iff.mp hm
  have h := DFinsupp.mem_support_iff.mp hi
  rw [TensorProduct.directSumLeft_tmul, hz, TensorProduct.zero_tmul] at h
  exact h rfl

theorem inverseMap : InverseMap.{u, v, w, t} := by
  classical
  intro R _ E M _ _ N _ _
  apply DirectSum.linearMap_ext R
  intro i
  apply TensorProduct.ext'
  intro x n
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.directSumLeft_symm_lof_tmul, DirectSum.toModule_lof,
    TensorProduct.map_tmul, LinearMap.id_apply]

theorem inverseFiniteSum : InverseFiniteSum.{u, v, w, t} := by
  classical
  intro R _ E M _ _ N _ _ z
  have h := LinearMap.congr_fun (inverseMap R E M N) z
  exact h.trans (D07.Ch22.FreeDirectSums.directSumMapFormula R E
    (fun i => M i ⊗[R] N) ((DirectSum E M) ⊗[R] N)
    (fun i => TensorProduct.map (DirectSum.lof R E M i) (LinearMap.id : N →ₗ[R] N))
    _ (fun i x => by simp only [DirectSum.toModule_lof]) z)

theorem inverseIdentities : InverseIdentities.{u, v, w, t} := by
  classical
  intro R _ E M _ _ N _ _
  exact ⟨(TensorProduct.directSumLeft R R M N).symm_apply_apply,
    (TensorProduct.directSumLeft R R M N).apply_symm_apply⟩

theorem freeTensor : FreeTensor.{u, v, t} := by
  classical
  intro R _ E N _ _
  exact ⟨TensorProduct.finsuppScalarLeft R N E,
    TensorProduct.finsuppScalarLeft_apply_tmul_apply,
    TensorProduct.finsuppScalarLeft_symm_apply_single⟩

/-- Transport finite function spaces to finite-support functions, take the
product coordinates, and return to the finite function model. -/
theorem finiteFreeTensor : FiniteFreeTensor.{u} := by
  intro R _ a b
  let e := (TensorProduct.congr (Finsupp.linearEquivFunOnFinite R R (Fin a)).symm
      (Finsupp.linearEquivFunOnFinite R R (Fin b)).symm).trans
    ((finsuppTensorFinsupp' R (Fin a) (Fin b)).trans
      ((Finsupp.linearEquivFunOnFinite R R (Fin a × Fin b)).trans
        (LinearEquiv.funCongrLeft R R finProdFinEquiv.symm)))
  refine ⟨e, ?_⟩
  intro f g i j
  simp [e, LinearEquiv.funCongrLeft]

theorem productBasis : ProductBasis.{u, w, t} := by
  intro R _ M _ _ N _ _ a b bm bn
  exact ⟨bm.tensorProduct bn, fun i j => Module.Basis.tensorProduct_apply bm bn i j⟩

theorem finiteRankInvariant : FiniteRankInvariant.{u} := by
  intro R _ _ a b e
  exact eq_of_fin_equiv R e

theorem rankMultiplication : RankMultiplication.{u, w, t} := by
  intro R _ _ M _ _ _ _ N _ _ _ _
  let bm := Module.Free.chooseBasis R M
  let bn := Module.Free.chooseBasis R N
  rw [Module.finrank_eq_card_basis (bm.tensorProduct bn), Fintype.card_prod,
    ← Module.finrank_eq_card_basis bm, ← Module.finrank_eq_card_basis bn]

theorem finiteBasisRank : FiniteBasisRank.{u, w} := by
  intro R _ _ M _ _ a b
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b

theorem zeroRingModules : ZeroRingModules.{u, w} := by
  intro R _ _ M _ _ x
  calc
    x = (1 : R) • x := (one_smul R x).symm
    _ = (0 : R) • x := congrArg (fun r : R => r • x) (Subsingleton.elim _ _)
    _ = 0 := zero_smul R x

theorem zeroRingSizes : ZeroRingSizes.{u} := by
  intro R _ _ a b
  exact ⟨LinearEquiv.ofSubsingleton (R := R) (Fin a → R) (Fin b → R)⟩

end D07.Ch22.TensorDirectSums
