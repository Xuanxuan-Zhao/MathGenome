import MathGenome.Internal.Specs.D07.Ch22.TensorFunctor

/-!
K07.22.tensor_functor. The canonical maps are constructed by tensor lifts;
no bases, ranks, or nonzero scalars are needed. Elementary-tensor formulas
and extensionality give all functor and naturality laws. The associator's
inverse and both iterations' additive generation are explicit below.
-/

noncomputable section
universe u v w t a b c d e f q
namespace D07.Ch22.TensorFunctor
open Specs.D07.Ch22.TensorFunctor
open scoped TensorProduct

theorem mapConstruction : MapConstruction.{u, v, w, a, b} := by
  intro R _ M _ _ N _ _ M' _ _ N' _ _ f g
  refine ⟨TensorProduct.map f g, fun _ _ => rfl, ?_⟩
  intro F hF
  exact TensorProduct.ext' hF

theorem mapFormula : MapFormula.{u, v, w, a, b} := by
  intro R _ M _ _ N _ _ M' _ _ N' _ _ f g m n
  rfl

theorem mapComposition : MapComposition.{u, v, w, a, b, d, e} := by
  intro R _ M _ _ N _ _ M' _ _ N' _ _ M'' _ _ N'' _ _ f g f' g'
  exact TensorProduct.map_comp f' g' f g

theorem mapIdentity : MapIdentity.{u, v, w} := by
  intro R _ M _ _ N _ _
  exact TensorProduct.map_id

theorem mapAdditivity : MapAdditivity.{u, v, w, a, b} := by
  intro R _ M _ _ N _ _ M' _ _ N' _ _ f f' g g'
  exact ⟨TensorProduct.map_add_left f f' g, TensorProduct.map_add_right f g g',
    TensorProduct.map_zero_left g, TensorProduct.map_zero_right f⟩

theorem tensorExt : TensorExt.{u, v, w, t} := by
  intro R _ M _ _ N _ _ P _ _ F G h
  exact TensorProduct.ext' h

theorem commIsomorphism : CommIsomorphism.{u, v, w} := by
  intro R _ M _ _ N _ _
  refine ⟨TensorProduct.comm R M N, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, ?_⟩
  intro E hE
  apply LinearEquiv.toLinearMap_injective
  exact TensorProduct.ext' hE.1

theorem commInvolution : CommInvolution.{u, v, w} := by
  intro R _ M _ _ N _ _
  exact TensorProduct.comm_comp_comm R M N

theorem commNaturality : CommNaturality.{u, v, w, a, b} := by
  intro R _ M _ _ N _ _ M' _ _ N' _ _ f g
  exact TensorProduct.map_comp_comm_eq g f

theorem assocIsomorphism : AssocIsomorphism.{u, v, w, t} := by
  intro R _ M _ _ N _ _ P _ _
  refine ⟨TensorProduct.assoc R M N P, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
  intro E hE
  apply LinearEquiv.toLinearMap_injective
  exact TensorProduct.ext_threefold hE.1

theorem iteratedGenerators : IteratedGenerators.{u, v, w, t} := by
  intro R _ M _ _ N _ _ P _ _
  constructor
  · apply top_unique
    intro x hx
    clear hx
    induction x using TensorProduct.inductionOn with
    | tmul y p =>
      induction y using TensorProduct.inductionOn with
      | tmul m n => exact AddSubgroup.subset_closure ⟨m, n, p, rfl⟩
      | add y z hy hz =>
        simpa only [TensorProduct.add_tmul] using AddSubgroup.add_mem _ hy hz
    | add x y hx hy => exact AddSubgroup.add_mem _ hx hy
  · apply top_unique
    intro x hx
    clear hx
    induction x using TensorProduct.inductionOn with
    | tmul m y =>
      induction y using TensorProduct.inductionOn with
      | tmul n p => exact AddSubgroup.subset_closure ⟨m, n, p, rfl⟩
      | add y z hy hz =>
        simpa only [TensorProduct.tmul_add] using AddSubgroup.add_mem _ hy hz
    | add x y hx hy => exact AddSubgroup.add_mem _ hx hy

theorem iteratedExt : IteratedExt.{u, v, w, t, q} := by
  intro R _ M _ _ N _ _ P _ _ Q _ _
  exact ⟨fun _ _ h => TensorProduct.ext_threefold h,
    fun _ _ h => TensorProduct.ext_threefold' h⟩

theorem assocNaturality : AssocNaturality.{u, v, w, t, a, b, c} := by
  intro R _ M _ _ N _ _ P _ _ M' _ _ N' _ _ P' _ _ f g h
  exact TensorProduct.map_map_comp_assoc_eq f g h

theorem unitIsomorphism : UnitIsomorphism.{u, v} := by
  intro R _ M _ _
  refine ⟨TensorProduct.lid R M, ⟨fun _ _ => rfl, fun _ => rfl⟩, ?_⟩
  intro E hE
  apply LinearEquiv.toLinearMap_injective
  exact TensorProduct.ext' hE.1

theorem unitBalance : UnitBalance.{u, v} := by
  intro R _ M _ _ r m
  simpa only [smul_eq_mul, mul_one] using
    (TensorProduct.smul_tmul r (1 : R) m).symm

theorem unitNaturality : UnitNaturality.{u, v, a} := by
  intro R _ M _ _ M' _ _ f
  apply TensorProduct.ext'
  intro r m
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, map_smul]

end D07.Ch22.TensorFunctor
