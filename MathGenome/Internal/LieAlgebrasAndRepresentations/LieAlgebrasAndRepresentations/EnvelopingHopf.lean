import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.EnvelopingHopf
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Enveloping
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Tactic.NoncommRing

namespace LieAlgebrasAndRepresentations.EnvelopingHopf
open _root_.Shared.Lie
open scoped TensorProduct
open MulOpposite
open TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v
variable (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]

/-- The primitive Lie map into the tensor square. -/
def primitive : g →ₗ⁅k⁆ U k g ⊗[k] U k g where
  toLinearMap :=
    (Algebra.TensorProduct.includeLeft : U k g →ₐ[k] U k g ⊗[k] U k g).toLinearMap.comp
      (inclusion k g).toLinearMap +
    (Algebra.TensorProduct.includeRight : U k g →ₐ[k] U k g ⊗[k] U k g).toLinearMap.comp
      (inclusion k g).toLinearMap
  map_lie' := by
    intro x y
    change inclusion k g ⁅x,y⁆ ⊗ₜ[k] (1 : U k g) +
      (1 : U k g) ⊗ₜ[k] inclusion k g ⁅x,y⁆ =
      ⁅inclusion k g x ⊗ₜ[k] (1 : U k g) + (1 : U k g) ⊗ₜ[k] inclusion k g x,
        inclusion k g y ⊗ₜ[k] (1 : U k g) + (1 : U k g) ⊗ₜ[k] inclusion k g y⁆
    rw [(inclusion k g).map_lie]
    simp only [LieRing.of_associative_ring_bracket, sub_tmul, tmul_sub,
      add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    abel

/-- Coproduct constructed by the universal property. -/
def coproduct : U k g →ₐ[k] U k g ⊗[k] U k g :=
  UniversalEnvelopingAlgebra.lift k (primitive k g)

@[simp] theorem coproduct_inclusion (x : g) : coproduct k g (inclusion k g x) =
    inclusion k g x ⊗ₜ[k] (1 : U k g) + (1 : U k g) ⊗ₜ[k] inclusion k g x :=
  UniversalEnvelopingAlgebra.lift_ι_apply k (primitive k g) x

/-- Negation of the generators is a Lie map to the opposite algebra. -/
def negativeOpposite : g →ₗ⁅k⁆ (U k g)ᵐᵒᵖ where
  toLinearMap := (MulOpposite.opLinearEquiv k).toLinearMap.comp (-(inclusion k g).toLinearMap)
  map_lie' := by
    intro x y
    change op (-inclusion k g ⁅x,y⁆) = ⁅op (-inclusion k g x), op (-inclusion k g y)⁆
    rw [(inclusion k g).map_lie]
    simp only [LieRing.of_associative_ring_bracket, ← op_mul, ← op_sub]
    congr 1
    noncomm_ring

/-- The universal anti-homomorphism, before proving it is invertible. -/
def antipodeMap : U k g →ₗ[k] U k g :=
  (MulOpposite.opLinearEquiv k).symm.toLinearMap.comp
    (UniversalEnvelopingAlgebra.lift k (negativeOpposite k g)).toLinearMap

@[simp] theorem antipodeMap_inclusion (x : g) :
    antipodeMap k g (inclusion k g x) = -inclusion k g x := by
  change unop (UniversalEnvelopingAlgebra.lift k (negativeOpposite k g) (inclusion k g x)) = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

@[simp] theorem antipodeMap_one : antipodeMap k g 1 = 1 := by
  change unop (UniversalEnvelopingAlgebra.lift k (negativeOpposite k g) 1) = _
  rw [map_one]
  rfl

@[simp] theorem antipodeMap_mul (a b : U k g) :
    antipodeMap k g (a*b) = antipodeMap k g b * antipodeMap k g a := by
  change unop (UniversalEnvelopingAlgebra.lift k (negativeOpposite k g) (a*b)) = _
  rw [map_mul, unop_mul]
  rfl

@[simp] theorem antipodeMap_scalar (r : k) :
    antipodeMap k g (algebraMap k (U k g) r) = algebraMap k (U k g) r := by
  change unop (UniversalEnvelopingAlgebra.lift k (negativeOpposite k g)
    (algebraMap k (U k g) r)) = _
  rw [AlgHom.commutes]
  rfl

theorem antipodeMap_involutive : Function.Involutive (antipodeMap k g) := by
  intro a
  induction a using enveloping_induction k g with
  | scalar r => simp
  | generator x => simp only [antipodeMap_inclusion, map_neg, neg_neg]
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- The antipode is its own inverse. -/
def antipode : U k g ≃ₗ[k] U k g :=
  { antipodeMap k g with
    invFun := antipodeMap k g
    left_inv := antipodeMap_involutive k g
    right_inv := antipodeMap_involutive k g }

/-- The two iterated coproducts agree by their values on the generators. -/
theorem coassociative (a : U k g) :
    TensorProduct.assoc k (U k g) (U k g) (U k g)
      (TensorProduct.map (coproduct k g).toLinearMap LinearMap.id (coproduct k g a)) =
    TensorProduct.map LinearMap.id (coproduct k g).toLinearMap (coproduct k g a) := by
  have h :
      (Algebra.TensorProduct.assoc k k k (U k g) (U k g) (U k g)).toAlgHom.comp
        ((Algebra.TensorProduct.map (coproduct k g) (AlgHom.id k (U k g))).comp
          (coproduct k g)) =
      (Algebra.TensorProduct.map (AlgHom.id k (U k g)) (coproduct k g)).comp
        (coproduct k g) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change (Algebra.TensorProduct.assoc k k k (U k g) (U k g) (U k g))
      (Algebra.TensorProduct.map (coproduct k g) (AlgHom.id k (U k g))
        (coproduct k g (inclusion k g x))) =
      Algebra.TensorProduct.map (AlgHom.id k (U k g)) (coproduct k g)
        (coproduct k g (inclusion k g x))
    simp only [coproduct_inclusion, map_add, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, map_one, Algebra.TensorProduct.one_def, add_tmul, tmul_add,
      Algebra.TensorProduct.assoc_tmul]
    abel
  exact DFunLike.congr_fun h a

/-- The augmentation is the left counit. -/
theorem counit_left (a : U k g) :
    TensorProduct.lid k (U k g)
      (TensorProduct.map (augmentation k g).toLinearMap LinearMap.id (coproduct k g a)) = a := by
  have h : (Algebra.TensorProduct.lid k (U k g)).toAlgHom.comp
      ((Algebra.TensorProduct.map (augmentation k g) (AlgHom.id k (U k g))).comp
        (coproduct k g)) = AlgHom.id k (U k g) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change Algebra.TensorProduct.lid k (U k g)
      (Algebra.TensorProduct.map (augmentation k g) (AlgHom.id k (U k g))
        (coproduct k g (inclusion k g x))) = inclusion k g x
    simp only [coproduct_inclusion, map_add, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, (augmentation_properties k g).1, map_one,
      zero_tmul, zero_add, Algebra.TensorProduct.lid_tmul, one_smul]
  exact DFunLike.congr_fun h a

/-- The augmentation is the right counit. -/
theorem counit_right (a : U k g) :
    TensorProduct.rid k (U k g)
      (TensorProduct.map LinearMap.id (augmentation k g).toLinearMap (coproduct k g a)) = a := by
  have h : (Algebra.TensorProduct.rid k k (U k g)).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id k (U k g)) (augmentation k g)).comp
        (coproduct k g)) = AlgHom.id k (U k g) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change Algebra.TensorProduct.rid k k (U k g)
      (Algebra.TensorProduct.map (AlgHom.id k (U k g)) (augmentation k g)
        (coproduct k g (inclusion k g x))) = inclusion k g x
    simp only [coproduct_inclusion, map_add, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, (augmentation_properties k g).1, map_one,
      tmul_zero, add_zero, Algebra.TensorProduct.rid_tmul, one_smul]
  exact DFunLike.congr_fun h a

/-- Multiplication after applying the antipode in the left tensor factor. -/
def leftFold : U k g ⊗[k] U k g →ₗ[k] U k g :=
  (LinearMap.mul' k (U k g)).comp
    (TensorProduct.map (antipodeMap k g) LinearMap.id)

/-- Multiplication after applying the antipode in the right tensor factor. -/
def rightFold : U k g ⊗[k] U k g →ₗ[k] U k g :=
  (LinearMap.mul' k (U k g)).comp
    (TensorProduct.map LinearMap.id (antipodeMap k g))

@[simp] theorem leftFold_tmul (a b : U k g) :
    leftFold k g (a ⊗ₜ[k] b) = antipodeMap k g a * b := rfl

@[simp] theorem rightFold_tmul (a b : U k g) :
    rightFold k g (a ⊗ₜ[k] b) = a * antipodeMap k g b := rfl

/-- The two terms cancel after applying the left antipode contraction. -/
theorem leftFold_primitive_mul (x : g) (t : U k g ⊗[k] U k g) :
    leftFold k g
      ((inclusion k g x ⊗ₜ[k] (1 : U k g) + (1 : U k g) ⊗ₜ[k] inclusion k g x) * t) = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_add,
      leftFold_tmul, antipodeMap_mul, antipodeMap_inclusion]
    noncomm_ring
  | add s t hs ht => simp only [mul_add, map_add, hs, ht, add_zero]

/-- The right contraction of a primitive multiple is a commutator. -/
theorem rightFold_primitive_mul (x : g) (t : U k g ⊗[k] U k g) :
    rightFold k g
      ((inclusion k g x ⊗ₜ[k] (1 : U k g) + (1 : U k g) ⊗ₜ[k] inclusion k g x) * t) =
    inclusion k g x * rightFold k g t - rightFold k g t * inclusion k g x := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_add,
      rightFold_tmul, antipodeMap_mul, antipodeMap_inclusion]
    noncomm_ring
  | add s t hs ht =>
    simp only [mul_add, map_add, hs, ht]
    noncomm_ring

/-- Linear maps on the enveloping algebra are determined by all words.
This uses the accepted exhaustive word filtration, rather than PBW. -/
theorem linearMap_ext_words {f h : U k g →ₗ[k] U k g}
    (hw : ∀ xs : List g, f (word k g xs) = h (word k g xs)) : f = h := by
  ext a
  obtain ⟨m, ha⟩ := filtration_exhaustive k g a
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨xs, _, rfl⟩ := ha
    exact hw xs
  | zero => simp only [map_zero]
  | add a b ha hb iha ihb => simp only [map_add, iha, ihb]
  | smul r a ha ih => simp only [map_smul, ih]

/-- The left antipode identity, proved on words and then by linearity. -/
theorem antipode_left (a : U k g) :
    leftFold k g (coproduct k g a) = algebraMap k (U k g) (augmentation k g a) := by
  have h : (leftFold k g).comp (coproduct k g).toLinearMap =
      (Algebra.linearMap k (U k g)).comp (augmentation k g).toLinearMap := by
    apply linearMap_ext_words k g
    intro xs
    change leftFold k g (coproduct k g (word k g xs)) =
      algebraMap k (U k g) (augmentation k g (word k g xs))
    cases xs with
    | nil =>
      simp only [word, List.map_nil, List.prod_nil, map_one,
        Algebra.TensorProduct.one_def, leftFold_tmul, antipodeMap_one, one_mul]
    | cons x xs =>
      have hw : word k g (x :: xs) = inclusion k g x * word k g xs := rfl
      rw [hw, map_mul, coproduct_inclusion, leftFold_primitive_mul, map_mul,
        (augmentation_properties k g).1, zero_mul, map_zero]
  exact DFunLike.congr_fun h a

/-- The right antipode identity. Centrality of scalars closes the word step. -/
theorem antipode_right (a : U k g) :
    rightFold k g (coproduct k g a) = algebraMap k (U k g) (augmentation k g a) := by
  have h : (rightFold k g).comp (coproduct k g).toLinearMap =
      (Algebra.linearMap k (U k g)).comp (augmentation k g).toLinearMap := by
    apply linearMap_ext_words k g
    intro xs
    change rightFold k g (coproduct k g (word k g xs)) =
      algebraMap k (U k g) (augmentation k g (word k g xs))
    induction xs with
    | nil =>
      simp only [word, List.map_nil, List.prod_nil, map_one,
        Algebra.TensorProduct.one_def, rightFold_tmul, antipodeMap_one, one_mul]
    | cons x xs ih =>
      have hw : word k g (x :: xs) = inclusion k g x * word k g xs := rfl
      rw [hw, map_mul, coproduct_inclusion, rightFold_primitive_mul, ih,
        map_mul, (augmentation_properties k g).1, zero_mul, map_zero]
      exact sub_eq_zero.mpr (Algebra.commutes (augmentation k g (word k g xs))
        (inclusion k g x)).symm
  exact DFunLike.congr_fun h a

/-- LA A06: the canonical tensor quotient admits all the stated Hopf maps
and identities over every field. -/
theorem hopf_spec : Specs.LieAlgebrasAndRepresentations.EnvelopingHopf.hopfExpected.{u,v} := by
  intro k g _ _ _
  refine ⟨coproduct k g, augmentation k g, antipode k g, ?_⟩
  exact ⟨coproduct_inclusion k g, (augmentation_properties k g).1,
    antipodeMap_inclusion k g, antipodeMap_one k g, antipodeMap_mul k g,
    coassociative k g, counit_left k g, counit_right k g,
    antipode_left k g, antipode_right k g⟩

end LieAlgebrasAndRepresentations.EnvelopingHopf
