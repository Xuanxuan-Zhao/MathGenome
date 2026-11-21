import MathGenome.Internal.Specs.D05.M03.Isomorphism
import MathGenome.Internal.Specs.D05.M15.TensorMaps
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
Independent statements for K05.15.associativity_symmetry, paper.tex:2763–2769.
All spaces are arbitrary algebraic vector spaces over an arbitrary field.
The equivalences are between the existing tensor products, with their elementary
formulas fixed, rather than equalities of underlying types. A finite tensor
bracketing records the elementary family in an arbitrary binary parenthesization;
its unit is the scalar field with distinguished elementary tensor 1.
-/

namespace Specs.D05.M15.AssociativitySymmetry

open scoped TensorProduct
universe u v w x

/-- Canonical associativity equivalence, with the bracketing direction fixed. -/
def associator_type :=
  ∀ (K : Type u) (U : Type v) (V : Type w) (W : Type x)
    [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ((U ⊗[K] V) ⊗[K] W) ≃ₗ[K] (U ⊗[K] (V ⊗[K] W))

def associator_value : associator_type.{u, v, w, x} :=
  fun K U V W _ _ _ _ _ _ _ => TensorProduct.assoc K U V W

/-- Canonical interchange of the two factors. -/
def flip_type :=
  ∀ (K : Type u) (V : Type v) (W : Type w)
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    (V ⊗[K] W) ≃ₗ[K] (W ⊗[K] V)

def flip_value : flip_type.{u, v, w} :=
  fun K V W _ _ _ _ _ => TensorProduct.comm K V W

/-- The field is the left tensor unit. -/
def leftUnit_type :=
  ∀ (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V],
    (K ⊗[K] V) ≃ₗ[K] V

def leftUnit_value : leftUnit_type.{u, v} :=
  fun K V _ _ _ => TensorProduct.lid K V

section ThreeFactors

/-- The first displayed assignment is an actual linear isomorphism. -/
def associator_apply : Prop :=
  ∀ {K U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W],
  ∀ (u : U) (v : V) (w : W),
    TensorProduct.assoc K U V W ((u ⊗ₜ[K] v) ⊗ₜ[K] w) =
      u ⊗ₜ[K] (v ⊗ₜ[K] w)

def associator_inverse_apply : Prop :=
  ∀ {K U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W],
  ∀ (u : U) (v : V) (w : W),
    (TensorProduct.assoc K U V W).symm (u ⊗ₜ[K] (v ⊗ₜ[K] w)) =
      (u ⊗ₜ[K] v) ⊗ₜ[K] w

/-- The reverse bracketing is inverse on all tensors, not just pure tensors. -/
def associator_inverse_laws : Prop :=
  ∀ {K U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W],
  (TensorProduct.assoc K U V W).symm.toLinearMap.comp
      (TensorProduct.assoc K U V W).toLinearMap = LinearMap.id ∧
  (TensorProduct.assoc K U V W).toLinearMap.comp
      (TensorProduct.assoc K U V W).symm.toLinearMap = LinearMap.id

/-- The elementary assignment determines the entire map uniquely. -/
def associator_unique : Prop :=
  ∀ {K U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W],
  ∀ f : ((U ⊗[K] V) ⊗[K] W) →ₗ[K] (U ⊗[K] (V ⊗[K] W)),
    (∀ u v w, f ((u ⊗ₜ[K] v) ⊗ₜ[K] w) = u ⊗ₜ[K] (v ⊗ₜ[K] w)) →
      f = (TensorProduct.assoc K U V W).toLinearMap
end ThreeFactors

section TwoFactors

def flip_apply : Prop :=
  ∀ {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (v : V) (w : W), TensorProduct.comm K V W (v ⊗ₜ[K] w) = w ⊗ₜ[K] v

/-- The inverse flip is the flip with the factors interchanged. -/
def flip_inverse : Prop :=
  ∀ {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  (TensorProduct.comm K V W).symm = TensorProduct.comm K W V

def flip_involutive : Prop :=
  ∀ {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  (TensorProduct.comm K W V).toLinearMap.comp
    (TensorProduct.comm K V W).toLinearMap = LinearMap.id

def flip_unique : Prop :=
  ∀ {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ f : (V ⊗[K] W) →ₗ[K] (W ⊗[K] V),
    (∀ v w, f (v ⊗ₜ[K] w) = w ⊗ₜ[K] v) →
      f = (TensorProduct.comm K V W).toLinearMap
end TwoFactors

section Unit

def leftUnit_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (a : K) (v : V), TensorProduct.lid K V (a ⊗ₜ[K] v) = a • v

def leftUnit_inverse_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ v : V, (TensorProduct.lid K V).symm v = (1 : K) ⊗ₜ[K] v

def scalar_tensor_identity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ (a : K) (v : V), a ⊗ₜ[K] v = (1 : K) ⊗ₜ[K] (a • v)

/-- Both unit inverse identities, including on non-elementary tensors. -/
def leftUnit_inverse_laws : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  (TensorProduct.lid K V).symm.toLinearMap.comp
      (TensorProduct.lid K V).toLinearMap = LinearMap.id ∧
  (TensorProduct.lid K V).toLinearMap.comp
      (TensorProduct.lid K V).symm.toLinearMap = LinearMap.id

def leftUnit_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
  ∀ f : (K ⊗[K] V) →ₗ[K] V,
    (∀ a v, f (a ⊗ₜ[K] v) = a • v) → f = (TensorProduct.lid K V).toLinearMap
end Unit

/-- A finite expression made of arbitrary vector spaces, scalar units and binary
tensor products. Indexing by the actual space keeps its existing instances. -/
inductive TensorBracketing (K : Type u) [Field K] :
    (M : Type u) → [AddCommGroup M] → [Module K M] → Type (u + 1)
  | leaf (M : Type u) [AddCommGroup M] [Module K M] : TensorBracketing K M
  | unit : TensorBracketing K K
  | node {M N : Type u} [AddCommGroup M] [Module K M]
      [AddCommGroup N] [Module K N] :
      TensorBracketing K M → TensorBracketing K N → TensorBracketing K (M ⊗[K] N)

namespace TensorBracketing
variable {K : Type u} [Field K]

/-- One independently chosen vector at each leaf occurrence. -/
def Inputs : {M : Type u} → [AddCommGroup M] → [Module K M] →
    TensorBracketing K M → Type u
  | _, _, _, @TensorBracketing.leaf _ _ M _ _ => M
  | _, _, _, .unit => PUnit
  | _, _, _, @TensorBracketing.node _ _ M N _ _ _ _ s t => Inputs s × Inputs t

/-- The elementary tensor for any parenthesization; a nullary unit is 1. -/
def elementary : {M : Type u} → [AddCommGroup M] → [Module K M] →
    (t : TensorBracketing K M) → Inputs t → M
  | _, _, _, @TensorBracketing.leaf _ _ M _ _ => fun x => x
  | _, _, _, .unit => fun _ => 1
  | _, _, _, @TensorBracketing.node _ _ M N _ _ _ _ s t =>
      fun x => elementary s x.1 ⊗ₜ[K] elementary t x.2
end TensorBracketing

/-- General compatibility statement: maps along any two routes out of any finite
bracketing agree if their effects on elementary tensors agree. In particular this
applies to compositions of associators, flips, units and tensors of these maps.
No equality of routes or spanning certificate is assumed. -/
def rebracketing_coherence : Prop :=
  ∀ {K M : Type u} {H : Type v} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup H] [Module K H] (t : TensorBracketing K M)
    (f g : M →ₗ[K] H),
    (∀ x : t.Inputs, f (t.elementary x) = g (t.elementary x)) → f = g

end Specs.D05.M15.AssociativitySymmetry
