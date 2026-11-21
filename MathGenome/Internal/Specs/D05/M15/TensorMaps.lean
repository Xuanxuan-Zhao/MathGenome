import MathGenome.Internal.Specs.D05.M03.MapAlgebra
import MathGenome.Internal.Specs.D05.M15.TensorUniversal
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
Independent specifications for K05.15.tensor_maps, paper.tex:2735–2740.

All tensor products and linear maps are algebraic over the same arbitrary
field. The spaces may have arbitrary dimension, including dimension zero.
The canonical tensor model is the one fixed by the upstream tensor universal
property. Composition is written in the order used by `LinearMap.comp`.
The two separate additivity and homogeneity laws express linearity in either
map argument, not joint linearity of the pair of maps. The equivalence bridge
specifies both its forward linear map and its inverse on all tensors.
-/

namespace Specs.D05.M15.TensorMaps

open scoped TensorProduct
universe u v w x y

/-- The type of the induced map on the existing tensor spaces. -/
def tensorMap_type :=
  ∀ {K : Type u} {V : Type v} {W : Type w} {V' : Type x} {W' : Type y}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W'],
    (V →ₗ[K] V') → (W →ₗ[K] W') → (V ⊗[K] W) →ₗ[K] (V' ⊗[K] W')

def tensorMap_value : tensorMap_type.{u, v, w, x, y} :=
  fun {_ _ _ _ _} _ _ _ _ _ _ _ _ _ S T => TensorProduct.map S T

/-- The elementary formula is bilinear in the two input vectors. -/
def elementary_bilinear : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    ∃ b : V →ₗ[K] W →ₗ[K] (V' ⊗[K] W'),
      ∀ v w, b v w = S v ⊗ₜ[K] T w

/-- Tensoring maps has the prescribed value on every elementary tensor. -/
def map_apply : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W') (v : V) (w : W),
    TensorProduct.map S T (v ⊗ₜ[K] w) = S v ⊗ₜ[K] T w

/-- No other linear map has that elementary formula. Together with
`map_apply` this gives the full existence-and-uniqueness assertion. -/
def map_unique : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W')
    (F : (V ⊗[K] W) →ₗ[K] (V' ⊗[K] W')),
    (∀ v w, F (v ⊗ₜ[K] w) = S v ⊗ₜ[K] T w) → F = TensorProduct.map S T

/-- The composition calculation on elementary tensors. -/
def comp_apply : Prop :=
  ∀ {K V W V' W' V'' W'' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [AddCommGroup V''] [Module K V''] [AddCommGroup W''] [Module K W'']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W')
    (S' : V' →ₗ[K] V'') (T' : W' →ₗ[K] W'') (v : V) (w : W),
    TensorProduct.map S' T' (TensorProduct.map S T (v ⊗ₜ[K] w)) =
      S' (S v) ⊗ₜ[K] T' (T w)

/-- Functoriality as equality of linear maps on the whole tensor space. -/
def map_comp : Prop :=
  ∀ {K V W V' W' V'' W'' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [AddCommGroup V''] [Module K V''] [AddCommGroup W''] [Module K W'']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W')
    (S' : V' →ₗ[K] V'') (T' : W' →ₗ[K] W''),
    (TensorProduct.map S' T').comp (TensorProduct.map S T) =
      TensorProduct.map (S'.comp S) (T'.comp T)

def map_id : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.id : W →ₗ[K] W) =
      (LinearMap.id : (V ⊗[K] W) →ₗ[K] (V ⊗[K] W))

def map_add_left : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S₁ S₂ : V →ₗ[K] V') (T : W →ₗ[K] W'),
    TensorProduct.map (S₁ + S₂) T = TensorProduct.map S₁ T + TensorProduct.map S₂ T

def map_add_right : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V →ₗ[K] V') (T₁ T₂ : W →ₗ[K] W'),
    TensorProduct.map S (T₁ + T₂) = TensorProduct.map S T₁ + TensorProduct.map S T₂

def map_smul_left : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (a : K) (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    TensorProduct.map (a • S) T = a • TensorProduct.map S T

def map_smul_right : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (a : K) (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    TensorProduct.map S (a • T) = a • TensorProduct.map S T

/-- Tensoring two linear isomorphisms gives an actual linear isomorphism. -/
def tensorEquiv_type :=
  ∀ {K : Type u} {V : Type v} {W : Type w} {V' : Type x} {W' : Type y}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W'],
    (V ≃ₗ[K] V') → (W ≃ₗ[K] W') → (V ⊗[K] W) ≃ₗ[K] (V' ⊗[K] W')

def tensorEquiv_value : tensorEquiv_type.{u, v, w, x, y} :=
  fun {_ _ _ _ _} _ _ _ _ _ _ _ _ _ S T => TensorProduct.congr S T

/-- Its underlying linear map is exactly the tensor of the original maps. -/
def tensorEquiv_forward : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V ≃ₗ[K] V') (T : W ≃ₗ[K] W'),
    (TensorProduct.congr S T).toLinearMap = TensorProduct.map S.toLinearMap T.toLinearMap

/-- Its inverse on all tensors is the tensor of the two inverse maps. -/
def tensorEquiv_inverse : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V ≃ₗ[K] V') (T : W ≃ₗ[K] W'),
    (TensorProduct.congr S T).symm.toLinearMap =
      TensorProduct.map S.symm.toLinearMap T.symm.toLinearMap

end Specs.D05.M15.TensorMaps
