import MathGenome.Internal.D05.M03.Isomorphism
import MathGenome.Internal.D05.M15.TensorMaps
import MathGenome.Internal.Specs.D05.M15.AssociativitySymmetry

/-! K05.15.associativity_symmetry: canonical isomorphisms and compatibility.

The library associator uses the universal property twice, in each direction;
its inverse identities are checked on elementary threefold tensors. The flip
and scalar unit are also universal-property constructions. No basis, finite
dimension or characteristic restriction is needed.
-/

namespace D05.M15.AssociativitySymmetry

open scoped TensorProduct
open Specs.D05.M15.AssociativitySymmetry (TensorBracketing)

/-- Reassociate three tensor factors to the right. -/
abbrev associator (K U V W : Type*) [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :
    ((U ⊗[K] V) ⊗[K] W) ≃ₗ[K] (U ⊗[K] (V ⊗[K] W)) :=
  TensorProduct.assoc K U V W

/-- Interchange two tensor factors. -/
abbrev flip (K V W : Type*) [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] :
    (V ⊗[K] W) ≃ₗ[K] (W ⊗[K] V) := TensorProduct.comm K V W

/-- Contract a scalar in the left tensor factor. -/
abbrev leftUnit (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    (K ⊗[K] V) ≃ₗ[K] V := TensorProduct.lid K V

theorem associator_apply : Specs.D05.M15.AssociativitySymmetry.associator_apply := by
  intro K U V W _ _ _ _ _ _ _ u v w
  rfl

theorem associator_inverse_apply :
    Specs.D05.M15.AssociativitySymmetry.associator_inverse_apply := by
  intro K U V W _ _ _ _ _ _ _ u v w
  rfl

theorem associator_inverse_laws :
    Specs.D05.M15.AssociativitySymmetry.associator_inverse_laws := by
  intro K U V W _ _ _ _ _ _ _
  exact ⟨(associator K U V W).symm_comp, (associator K U V W).comp_symm⟩

theorem associator_unique : Specs.D05.M15.AssociativitySymmetry.associator_unique := by
  intro K U V W _ _ _ _ _ _ _ f hf
  exact TensorProduct.ext_threefold hf

theorem flip_apply : Specs.D05.M15.AssociativitySymmetry.flip_apply := by
  intro K V W _ _ _ _ _ v w
  rfl

theorem flip_inverse : Specs.D05.M15.AssociativitySymmetry.flip_inverse := by
  intro K V W _ _ _ _ _
  rfl

theorem flip_involutive : Specs.D05.M15.AssociativitySymmetry.flip_involutive := by
  intro K V W _ _ _ _ _
  exact (flip K V W).symm_comp

theorem flip_unique : Specs.D05.M15.AssociativitySymmetry.flip_unique := by
  intro K V W _ _ _ _ _ f hf
  exact TensorProduct.ext' hf

theorem leftUnit_apply : Specs.D05.M15.AssociativitySymmetry.leftUnit_apply := by
  intro K V _ _ _ a v
  rfl

theorem leftUnit_inverse_apply :
    Specs.D05.M15.AssociativitySymmetry.leftUnit_inverse_apply := by
  intro K V _ _ _ v
  rfl

theorem scalar_tensor_identity :
    Specs.D05.M15.AssociativitySymmetry.scalar_tensor_identity := by
  intro K V _ _ _ a v
  simpa only [smul_eq_mul, mul_one] using
    (TensorProduct.smul_tmul (R := K) a (1 : K) v)

theorem leftUnit_inverse_laws :
    Specs.D05.M15.AssociativitySymmetry.leftUnit_inverse_laws := by
  intro K V _ _ _
  exact ⟨(leftUnit K V).symm_comp, (leftUnit K V).comp_symm⟩

theorem leftUnit_unique : Specs.D05.M15.AssociativitySymmetry.leftUnit_unique := by
  intro K V _ _ _ f hf
  exact TensorProduct.ext' hf

/-- Repeated use of tensor extensionality proves compatibility for every finite
binary bracketing. At a scalar unit, agreement on 1 suffices by linearity. -/
theorem rebracketing_coherence :
    Specs.D05.M15.AssociativitySymmetry.rebracketing_coherence := by
  intro K M H _ _ _ _ _ t
  induction t with
  | leaf M =>
      intro f g h
      exact LinearMap.ext h
  | unit =>
      intro f g h
      apply LinearMap.ext
      intro a
      have h1 : f 1 = g 1 := h PUnit.unit
      calc
        f a = f (a • (1 : K)) := by rw [smul_eq_mul, mul_one]
        _ = a • f 1 := f.map_smul a 1
        _ = a • g 1 := by rw [h1]
        _ = g (a • (1 : K)) := (g.map_smul a 1).symm
        _ = g a := by rw [smul_eq_mul, mul_one]
  | @node M N _ _ _ _ s t ihs iht =>
      intro f g h
      apply TensorProduct.ext'
      intro m n
      have hleft : ∀ y : t.Inputs,
          f (m ⊗ₜ[K] t.elementary y) = g (m ⊗ₜ[K] t.elementary y) := by
        intro y
        have e := ihs
          (f.comp ((TensorProduct.mk K M N).flip (t.elementary y)))
          (g.comp ((TensorProduct.mk K M N).flip (t.elementary y)))
          (fun x => h (x, y))
        exact LinearMap.congr_fun e m
      have e := iht (f.comp (TensorProduct.mk K M N m))
        (g.comp (TensorProduct.mk K M N m)) hleft
      exact LinearMap.congr_fun e n

end D05.M15.AssociativitySymmetry
