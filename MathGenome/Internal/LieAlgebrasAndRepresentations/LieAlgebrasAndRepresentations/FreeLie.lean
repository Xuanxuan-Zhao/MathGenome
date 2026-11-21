import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FreeLie
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Enveloping
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PBWSpecialization

/-! LA A07 (notes/005, lines 463–491).
The set-free Lie algebra on a basis of V supplies the vector-space-linear
universal property. The tensor and enveloping universal properties give inverse
algebra maps, and field PBW proves the induced Lie map is injective.
No dimension or characteristic restriction is imposed.
-/
noncomputable section
namespace LieAlgebrasAndRepresentations.FreeLie
universe u v w
variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

abbrev freeLieAlgebra := Free k V
abbrev linearGenerator := generator k V

@[simp] theorem generator_basis (i : BasisIndex k V) :
    generator k V (vectorBasis k V i) = FreeLieAlgebra.of k i :=
  (vectorBasis k V).constr_basis k _ i

@[simp] theorem extend_of {g : Type w} [LieRing g] [LieAlgebra k g]
    (f : V →ₗ[k] g) (i : BasisIndex k V) :
    extend k V f (FreeLieAlgebra.of k i) = f (vectorBasis k V i) :=
  FreeLieAlgebra.lift_of_apply _ _

@[simp] theorem extend_generator {g : Type w} [LieRing g] [LieAlgebra k g]
    (f : V →ₗ[k] g) : (extend k V f).toLinearMap.comp (generator k V) = f := by
  apply (vectorBasis k V).ext
  intro i
  simp

theorem linear_hom_ext {g : Type w} [LieRing g] [LieAlgebra k g]
    {F G : Free k V →ₗ⁅k⁆ g}
    (h : F.toLinearMap.comp (generator k V) = G.toLinearMap.comp (generator k V)) : F = G := by
  apply FreeLieAlgebra.hom_ext
  intro i
  have := LinearMap.congr_fun h (vectorBasis k V i)
  simpa using this

attribute [local instance 100] LieRing.ofAssociativeRing

@[simp] theorem tensorLieMap_generator :
    (tensorLieMap k V).toLinearMap.comp (generator k V) = TensorAlgebra.ι k :=
  extend_generator k V _

@[simp] theorem tensorLieMap_generator_apply (v : V) :
    tensorLieMap k V (generator k V v) = TensorAlgebra.ι k v :=
  LinearMap.congr_fun (tensorLieMap_generator k V) v

@[simp] theorem tensorMap_inclusion (x : Free k V) :
    tensorMap k V (Shared.Lie.inclusion k (Free k V) x) = tensorLieMap k V x :=
  UniversalEnvelopingAlgebra.lift_ι_apply k (tensorLieMap k V) x

@[simp] theorem tensorInverse_generator (v : V) :
    tensorInverse k V (TensorAlgebra.ι k v) =
      Shared.Lie.inclusion k (Free k V) (generator k V v) :=
  TensorAlgebra.lift_ι_apply _ _

theorem tensor_left_inverse : (tensorInverse k V).comp (tensorMap k V) = AlgHom.id k _ := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply FreeLieAlgebra.hom_ext
  intro i
  change tensorInverse k V (tensorMap k V (Shared.Lie.inclusion k (Free k V)
    (FreeLieAlgebra.of k i))) = Shared.Lie.inclusion k (Free k V) (FreeLieAlgebra.of k i)
  rw [tensorMap_inclusion]
  rw [show tensorLieMap k V (FreeLieAlgebra.of k i) = TensorAlgebra.ι k (vectorBasis k V i)
    from extend_of k V (TensorAlgebra.ι k) i]
  rw [tensorInverse_generator, generator_basis]

theorem tensor_right_inverse : (tensorMap k V).comp (tensorInverse k V) = AlgHom.id k _ := by
  apply TensorAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change tensorMap k V (tensorInverse k V (TensorAlgebra.ι k v)) = TensorAlgebra.ι k v
  rw [tensorInverse_generator, tensorMap_inclusion, tensorLieMap_generator_apply]

def tensorEquiv : Shared.Lie.U k (Free k V) ≃ₐ[k] TensorAlgebra k V :=
  AlgEquiv.ofAlgHom (tensorMap k V) (tensorInverse k V)
    (tensor_right_inverse k V) (tensor_left_inverse k V)

/-- The linear generator is faithful, as seen by mapping to the tensor algebra. -/
theorem generator_injective : Function.Injective (generator k V) := by
  intro x y hxy
  apply (TensorAlgebra.ι_inj k x y).mp
  simpa only [tensorLieMap_generator_apply] using congrArg (tensorLieMap k V) hxy

/-- The universal property also proves generation under linear combinations and brackets. -/
theorem generated : LieSubalgebra.lieSpan k (Free k V) (Set.range (generator k V)) = ⊤ := by
  let S := LieSubalgebra.lieSpan k (Free k V) (Set.range (generator k V))
  let f : V →ₗ[k] S := (generator k V).codRestrict S.toSubmodule
    (fun v => LieSubalgebra.subset_lieSpan (Set.mem_range_self v))
  have h : S.incl.comp (extend k V f) = (LieHom.id : Free k V →ₗ⁅k⁆ Free k V) := by
    apply linear_hom_ext k V
    ext v
    have hv := LinearMap.congr_fun (extend_generator k V f) v
    exact congrArg (fun z : S => (z : Free k V)) hv
  apply top_unique
  intro x _
  have hx := congrArg (fun F : Free k V →ₗ⁅k⁆ Free k V => F x) h
  change (extend k V f x : Free k V) = x at hx
  exact hx ▸ (extend k V f x).property

theorem tensorLieMap_injective : Function.Injective (tensorLieMap k V) := by
  let : LinearOrder (Module.Free.ChooseBasisIndex k (Free k V)) :=
    IsWellOrder.linearOrder WellOrderingRel
  have hi := LieAlgebrasAndRepresentations.PBW.inclusionInjective_spec k (Free k V)
    (Module.Free.ChooseBasisIndex k (Free k V)) (Module.Free.chooseBasis k (Free k V))
  intro x y h
  apply hi
  apply (tensorEquiv k V).injective
  exact (tensorMap_inclusion k V x).trans (h.trans (tensorMap_inclusion k V y).symm)

theorem tensorLieMap_range : (tensorLieMap k V).range =
    LieSubalgebra.lieSpan k (TensorAlgebra k V) (Set.range (TensorAlgebra.ι k : V →ₗ[k] _)) := by
  rw [LieHom.range_eq_map, ← generated k V, LieSubalgebra.map_lieSpan]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext v
  exact tensorLieMap_generator_apply k V v

theorem universal_spec : Specs.LieAlgebrasAndRepresentations.FreeLie.universalExpected.{u,v,w} := by
  intro k V _ _ _
  refine ⟨generator_injective k V, ?_⟩
  intro g _ _ f
  refine ⟨extend k V f, extend_generator k V f, ?_⟩
  intro F hF
  exact linear_hom_ext k V (hF.trans (extend_generator k V f).symm)

theorem tensor_spec : Specs.LieAlgebrasAndRepresentations.FreeLie.tensorExpected.{u,v} := by
  intro k V _ _ _
  refine ⟨tensorEquiv k V, rfl, rfl, ?_⟩
  intro v
  change tensorMap k V (Shared.Lie.inclusion k (Free k V) (generator k V v)) = _
  rw [tensorMap_inclusion, tensorLieMap_generator_apply]

theorem image_spec : Specs.LieAlgebrasAndRepresentations.FreeLie.imageExpected.{u,v} := by
  intro k V _ _ _
  refine ⟨?_, tensorLieMap_injective k V, tensorLieMap_range k V⟩
  apply DFunLike.ext
  intro x
  exact (tensorMap_inclusion k V x).symm

end LieAlgebrasAndRepresentations.FreeLie
