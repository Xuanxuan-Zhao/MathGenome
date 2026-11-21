import Mathlib.FieldTheory.Galois.Basic

/-!
Foundational conventions for Advanced Field Theory.
Source: notes/003/advanced-field-theory.tex, scope and conventions,
chapter 1 introductory paragraphs, and the introductions to chapters 2 and 3.
All intermediate fields below are Mathlib's literal `IntermediateField K L`.
The chosen `Algebra K L` records the specified embedding of the base field.
-/

universe u v w

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedVariables false

namespace Specs.AdvancedFieldTheory

/-- The group G = Gal(L/K); multiplication is composition. -/
def GaloisGroup_type := ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Type v

def GaloisGroup_value : GaloisGroup_type :=
  fun (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] => L ≃ₐ[K] L

/-- The group Q_M = Gal(M/K). -/
def stageGroup_type := ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L), Type v

def stageGroup_value : stageGroup_type :=
  fun {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) => M ≃ₐ[K] M

/-- The subgroup G_M fixing M pointwise. -/
def fixingSubgroup_type := ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L), Subgroup (L ≃ₐ[K] L)

def fixingSubgroup_value : fixingSubgroup_type :=
  fun {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) => M.fixingSubgroup

/-- The intermediate field L^H of elements fixed by H. -/
def fixedField_type := ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L)), IntermediateField K L

def fixedField_value : fixedField_type :=
  fun {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L)) => IntermediateField.fixedField H

/-- The field K(S) generated inside L by S and the base field. -/
def generatedField_type := ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (S : Set L), IntermediateField K L

def generatedField_value : generatedField_type :=
  fun {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (S : Set L) => IntermediateField.adjoin K S

/-- Represent an abstract embedded extension by its image inside L. -/
def embeddedField_type := ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L), IntermediateField K L

def embeddedField_value : embeddedField_type :=
  fun {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L) => i.fieldRange

/-- Transport the field and K-algebra operations to the embedded image. -/
def embeddingEquiv_type := ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L), E ≃ₐ[K] i.fieldRange

def embeddingEquiv_value : embeddingEquiv_type :=
  fun {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L) => i.equivFieldRange

/-- Identify G_M with the intrinsic automorphism group Gal(L/M). -/
def fixingSubgroupEquiv_type := ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L), M.fixingSubgroup ≃* (L ≃ₐ[M] L)

def fixingSubgroupEquiv_value : fixingSubgroupEquiv_type :=
  fun {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) => M.fixingSubgroupEquiv

/-- The chosen base map is an injective field homomorphism. -/
def baseMap_injective_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Function.Injective (algebraMap K L)

/-- Galois means algebraic, normal, and separable, including for infinite extensions. -/
def isGalois_iff_algebraic_normal_separable_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], IsGalois K L ↔ Algebra.IsAlgebraic K L ∧ Normal K L ∧ Algebra.IsSeparable K L

/-- Products apply the right factor first. -/
def galoisGroup_mul_apply_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (σ τ : L ≃ₐ[K] L) (x : L), (σ * τ) x = σ (τ x)

/-- Every member of G fixes the specified image of K. -/
def galoisGroup_fixes_base_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (a : K), σ (algebraMap K L a) = algebraMap K L a

/-- The lower scalar map is the restriction of the chosen base map. -/
def intermediate_baseMap_coe_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) (a : K), ((algebraMap K M a : M) : L) = algebraMap K L a

/-- The upper scalar map is literal inclusion. -/
def intermediate_topMap_apply_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) (x : M), algebraMap M L x = (x : L)

/-- The inclusion scalar structures form the usual field tower. -/
def intermediate_scalarTower_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L), IsScalarTower K M L

/-- Inclusions between intermediate fields preserve the ambient element. -/
def intermediate_inclusion_coe_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {M N : IntermediateField K L} (h : M ≤ N) (x : M), ((IntermediateField.inclusion h x : N) : L) = (x : L)

/-- G_M is exactly the subgroup fixing every element of M. -/
def mem_fixingSubgroup_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) (σ : L ≃ₐ[K] L), σ ∈ M.fixingSubgroup ↔ ∀ x ∈ M, σ x = x

/-- The intrinsic automorphism and the subgroup element have the same action. -/
def fixingSubgroupEquiv_apply_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) (σ : M.fixingSubgroup) (x : L), M.fixingSubgroupEquiv σ x = (σ : L ≃ₐ[K] L) x

/-- The fixed field has precisely the source fixed-element set. -/
def mem_fixedField_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L)) (x : L), x ∈ IntermediateField.fixedField H ↔ ∀ σ ∈ H, σ x = x

/-- The fixed field contains the specified image of K. -/
def fixedField_contains_base_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L)) (a : K), algebraMap K L a ∈ IntermediateField.fixedField H

/-- The fixed-element set is closed under all field operations (even inverse at zero). -/
def fixedField_operations_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L)), (0 : L) ∈ IntermediateField.fixedField H ∧
    (1 : L) ∈ IntermediateField.fixedField H ∧
    (∀ x y : L, x ∈ IntermediateField.fixedField H → y ∈ IntermediateField.fixedField H →
      x + y ∈ IntermediateField.fixedField H) ∧
    (∀ x : L, x ∈ IntermediateField.fixedField H → -x ∈ IntermediateField.fixedField H) ∧
    (∀ x y : L, x ∈ IntermediateField.fixedField H → y ∈ IntermediateField.fixedField H →
      x * y ∈ IntermediateField.fixedField H) ∧
    (∀ x : L, x ∈ IntermediateField.fixedField H → x⁻¹ ∈ IntermediateField.fixedField H)

/-- K(S) is the least intermediate field containing S. -/
def generatedField_le_iff_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (S : Set L) (M : IntermediateField K L), IntermediateField.adjoin K S ≤ M ↔ S ⊆ (M : Set L)

/-- Membership in the embedded image is actual image membership. -/
def mem_embeddedField_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L) (x : L), x ∈ i.fieldRange ↔ ∃ a : E, i a = x

/-- Transport to the image followed by inclusion is the original embedding. -/
def embeddingEquiv_coe_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L) (a : E), ((i.equivFieldRange a : i.fieldRange) : L) = i a

end Specs.AdvancedFieldTheory
