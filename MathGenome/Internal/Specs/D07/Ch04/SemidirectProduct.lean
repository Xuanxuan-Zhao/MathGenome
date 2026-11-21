import MathGenome.Internal.Specs.D07.Ch01.AutomorphismGroups
import MathGenome.Internal.Specs.D07.Ch04.DirectProducts
import Mathlib.GroupTheory.SemidirectProduct

/-!
Independent specification for `K07.04.semidirect_product`, paper.tex:785–809.
The canonical semidirect product is a structure with exactly two fields; its
coordinate equivalence identifies its carrier with the Cartesian product.
The action is by `h`, with automorphisms multiplied by composition, as in the
source. All groups, including trivial and infinite groups, are allowed.

The embeddings are bundled homomorphisms. Complementarity means bijectivity
of multiplication from the two range subgroups, hence unique factorization.
No quotient operation or extra normality assumption is used.
-/

namespace Specs.D07.Ch04.SemidirectProduct

universe u v

def ProductType : Type (max u v + 1) :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H],
    (H →* MulAut N) → Type (max u v)

abbrev productValue : ProductType.{u, v} := fun N H _ _ φ => _root_.SemidirectProduct N H φ

def GroupStructureType : Type (max u v + 1) :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    Group (productValue N H φ)

def groupStructureValue : GroupStructureType.{u, v} := fun _ _ _ _ _ => inferInstance

def CoordinatesType : Type (max u v + 1) :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    productValue N H φ ≃ N × H

def coordinatesValue : CoordinatesType.{u, v} := fun _ _ _ _ _ =>
  _root_.SemidirectProduct.equivProd

def InclusionNType : Type (max u v + 1) :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    N →* productValue N H φ

def inclusionNValue : InclusionNType.{u, v} := fun _ _ _ _ _ =>
  _root_.SemidirectProduct.inl

def InclusionHType : Type (max u v + 1) :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    H →* productValue N H φ

def inclusionHValue : InclusionHType.{u, v} := fun _ _ _ _ _ =>
  _root_.SemidirectProduct.inr

def ProjectionType : Type (max u v + 1) :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    productValue N H φ →* H

def projectionValue : ProjectionType.{u, v} := fun _ _ _ _ _ =>
  _root_.SemidirectProduct.rightHom

/-- The group law, identity and inverse in the original pair coordinates. -/
def Operations : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    (∀ x y : productValue N H φ,
      coordinatesValue N H φ (x * y) =
        (x.left * φ x.right y.left, x.right * y.right)) ∧
    coordinatesValue N H φ 1 = (1, 1) ∧
    (∀ x : productValue N H φ,
      coordinatesValue N H φ x⁻¹ = (φ x.right⁻¹ x.left⁻¹, x.right⁻¹))

def GroupLaws : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    Specs.D07.Ch01.GroupDefinition.groupAxiomsValue
      (productValue N H φ) (· * ·) 1 Inv.inv

def Embeddings : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    (∀ n : N, coordinatesValue N H φ (inclusionNValue N H φ n) = (n, 1)) ∧
    (∀ h : H, coordinatesValue N H φ (inclusionHValue N H φ h) = (1, h)) ∧
    Function.Injective (inclusionNValue N H φ) ∧
    Function.Injective (inclusionHValue N H φ)

def ProjectionLaws : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    (∀ x : productValue N H φ, projectionValue N H φ x = x.right) ∧
    Function.Surjective (projectionValue N H φ) ∧
    (projectionValue N H φ).ker = (inclusionNValue N H φ).range

def FirstFactorNormal : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    (inclusionNValue N H φ).range.Normal

def Factorization : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N)
    (x : productValue N H φ),
    x = inclusionNValue N H φ x.left * inclusionHValue N H φ x.right

def FactorsIntersectTrivially : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    (inclusionNValue N H φ).range ⊓ (inclusionHValue N H φ).range = ⊥

/-- This asserts existence and uniqueness of the subgroup factorization. -/
def SecondFactorComplement : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    (inclusionNValue N H φ).range.IsComplement' (inclusionHValue N H φ).range

/-- A pointwise trivial action gives the coordinatewise direct-product law. -/
def TrivialActionMultiplication : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    (∀ h : H, φ h = 1) → ∀ x y : productValue N H φ,
      coordinatesValue N H φ (x * y) =
        coordinatesValue N H φ x * coordinatesValue N H φ y

/-- The isomorphism is the identity on pair coordinates, not just an
unspecified abstract isomorphism. -/
def TrivialActionIso : Prop :=
  ∀ (N : Type u) (H : Type v) [Group N] [Group H] (φ : H →* MulAut N),
    (∀ h : H, φ h = 1) →
      ∃ e : productValue N H φ ≃* N × H,
        ∀ x : productValue N H φ, e x = coordinatesValue N H φ x

end Specs.D07.Ch04.SemidirectProduct
