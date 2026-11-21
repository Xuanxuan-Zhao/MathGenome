import MathGenome.Internal.Specs.D05.M15.TensorUniversal
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
Independent statements for K05.15.tensor_quotient, paper.tex:2774–2783.

Both factors may have arbitrary dimension over any field, including positive
characteristic. The denominator is the sum of the images of the natural
subspace tensor maps, rather than a tensor product regarded as a subset without
an inclusion. The upstream subspace-tensor inclusion theorem identifies these
images with the paper's `U ⊗ W` and `V ⊗ S`. No complement is part of the data.
-/

namespace Specs.D05.M15.TensorQuotient

open scoped TensorProduct

/-- The subspace denoted by `U ⊗ W + V ⊗ S` inside `V ⊗ W`. -/
def tensorRelations {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (U : Submodule K V) (S : Submodule K W) : Submodule K (V ⊗[K] W) :=
  LinearMap.range (TensorProduct.map U.subtype (LinearMap.id : W →ₗ[K] W)) ⊔
    LinearMap.range (TensorProduct.map (LinearMap.id : V →ₗ[K] V) S.subtype)

/-- The isomorphism exists and is uniquely determined by the canonical
representative formula, not by a choice of bases or complements. -/
def canonical_quotient_iso : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (U : Submodule K V) (S : Submodule K W),
    ∃! e : ((V ⧸ U) ⊗[K] (W ⧸ S)) ≃ₗ[K]
        ((V ⊗[K] W) ⧸ tensorRelations U S),
      ∀ (v : V) (w : W),
        e (U.mkQ v ⊗ₜ[K] S.mkQ w) = (tensorRelations U S).mkQ (v ⊗ₜ[K] w)

/-- The kernel of the tensor of the quotient maps is exactly the displayed sum. -/
def quotient_map_kernel : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (U : Submodule K V) (S : Submodule K W),
    LinearMap.ker (TensorProduct.map U.mkQ S.mkQ) = tensorRelations U S

/-- For the canonical isomorphism, its inverse is the descended tensor of
quotient maps, both on elementary tensors and as an equality of linear maps. -/
def inverse_quotient_formula : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (U : Submodule K V) (S : Submodule K W)
    (e : ((V ⧸ U) ⊗[K] (W ⧸ S)) ≃ₗ[K]
      ((V ⊗[K] W) ⧸ tensorRelations U S)),
    (∀ (v : V) (w : W),
      e (U.mkQ v ⊗ₜ[K] S.mkQ w) = (tensorRelations U S).mkQ (v ⊗ₜ[K] w)) →
    (∀ (v : V) (w : W),
      e.symm ((tensorRelations U S).mkQ (v ⊗ₜ[K] w)) = U.mkQ v ⊗ₜ[K] S.mkQ w) ∧
    e.symm.toLinearMap.comp (tensorRelations U S).mkQ = TensorProduct.map U.mkQ S.mkQ

/-- The class of an elementary tensor is independent of both representatives. -/
def representative_independence : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (U : Submodule K V) (S : Submodule K W) (v v' : V) (w w' : W),
    v' - v ∈ U → w' - w ∈ S →
    (tensorRelations U S).mkQ (v' ⊗ₜ[K] w') =
      (tensorRelations U S).mkQ (v ⊗ₜ[K] w)

end Specs.D05.M15.TensorQuotient
