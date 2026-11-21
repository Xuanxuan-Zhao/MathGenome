import MathGenome.Internal.Specs.D07.Ch12.AdjoinDefinition
import MathGenome.Internal.Specs.D07.Ch14.AutomorphismGroup
import Mathlib.FieldTheory.Galois.Basic

/-!
Independent specification of K07.14.fixed_field (paper.tex:4097–4106).
The chosen Algebra K L records the base embedding. Neither the extension
nor the subgroup is assumed finite, algebraic, normal, or separable.
The intermediate field E has its canonical inclusion into L and induced
K-algebra structure. The identification with Aut_E(L) keeps the same maps.
-/

universe u v

namespace Specs.D07.Ch14.FixedField

def FixedFieldType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Subgroup (L ≃ₐ[K] L) → IntermediateField K L

def fixedFieldValue : FixedFieldType.{u, v} :=
  fun _ _ _ _ _ H => IntermediateField.fixedField H

def FixingSubgroupType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    IntermediateField K L → Subgroup (L ≃ₐ[K] L)

def fixingSubgroupValue : FixingSubgroupType.{u, v} :=
  fun _ _ _ _ _ E => E.fixingSubgroup

def FixingSubgroupEquivType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L),
    fixingSubgroupValue K L E ≃* (L ≃ₐ[E] L)

def fixingSubgroupEquivValue : FixingSubgroupEquivType.{u, v} :=
  fun _ _ _ _ _ E => E.fixingSubgroupEquiv

/-- Exactly the source's fixed-element predicate, with every member of H. -/
def FixedFieldCarrier : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)),
    (fixedFieldValue K L H : Set L) = {x | ∀ σ ∈ H, σ x = x}

/-- The field includes the specified base and inherits the field operations. -/
def FixedFieldOperations : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)),
    let F := fixedFieldValue K L H
    (∀ k : K, algebraMap K L k ∈ F) ∧ (0 : L) ∈ F ∧ (1 : L) ∈ F ∧
      ∀ a ∈ F, ∀ b ∈ F, a - b ∈ F ∧ a * b ∈ F ∧ a⁻¹ ∈ F

def FixingSubgroupCarrier : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L),
    (fixingSubgroupValue K L E : Set (L ≃ₐ[K] L)) =
      {σ | ∀ x ∈ E, σ x = x}

/-- The ambient product is left function composition, as in the upstream Aut. -/
def FixingSubgroupOperations : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L),
    let G := fixingSubgroupValue K L E
    (1 : L ≃ₐ[K] L) ∈ G ∧
      ∀ σ ∈ G, ∀ τ ∈ G, σ * τ ∈ G ∧ σ⁻¹ ∈ G

/-- Both directions of the group isomorphism retain the underlying field maps.
Its type already asserts multiplicativity, bijectivity, and inverse laws. -/
def FixingSubgroupEquivMaps : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L),
    let e := fixingSubgroupEquivValue K L E
    (∀ (σ : fixingSubgroupValue K L E) (x : L), e σ x = σ.val x) ∧
      ∀ (τ : L ≃ₐ[E] L) (x : L), (e.symm τ).val x = τ x

end Specs.D07.Ch14.FixedField
