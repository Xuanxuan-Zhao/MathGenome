import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
# Common field-theory interfaces

We use the standard `IsGalois`, `IntermediateField`, and `AlgEquiv` structures.
No algebraicity or finiteness assumption is imposed on the definitions of
fixed fields, fixing subgroups, or generated fields. The group of an
intermediate field is available for every intermediate field, and is denoted
`Q_M` in the source when that field is Galois over the base.
-/

universe u v w

namespace AdvancedFieldTheory

/-- The group G = Gal(L/K); multiplication is composition. -/
abbrev GaloisGroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : Type v :=
  L ≃ₐ[K] L

/-- The group Q_M = Gal(M/K). -/
abbrev stageGroup {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) : Type v :=
  M ≃ₐ[K] M

/-- The subgroup G_M fixing M pointwise. -/
def fixingSubgroup {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) : Subgroup (L ≃ₐ[K] L) :=
  M.fixingSubgroup

/-- The intermediate field L^H of elements fixed by H. -/
def fixedField {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L)) : IntermediateField K L :=
  IntermediateField.fixedField H

/-- The field K(S) generated inside L by S and the base field. -/
def generatedField {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (S : Set L) : IntermediateField K L :=
  IntermediateField.adjoin K S

/-- Represent an abstract embedded extension by its image inside L. -/
def embeddedField {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L) : IntermediateField K L :=
  i.fieldRange

/-- Transport the field and K-algebra operations to the embedded image. -/
noncomputable def embeddingEquiv {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L) : E ≃ₐ[K] i.fieldRange :=
  i.equivFieldRange

/-- Identify G_M with the intrinsic automorphism group Gal(L/M). -/
def fixingSubgroupEquiv {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) : M.fixingSubgroup ≃* (L ≃ₐ[M] L) :=
  M.fixingSubgroupEquiv

/-- The chosen base map is an injective field homomorphism. -/
theorem baseMap_injective (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Function.Injective (algebraMap K L) := (algebraMap K L).injective

/-- Galois means algebraic, normal, and separable, including for infinite extensions. -/
theorem isGalois_iff_algebraic_normal_separable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    IsGalois K L ↔ Algebra.IsAlgebraic K L ∧ Normal K L ∧ Algebra.IsSeparable K L := by
  constructor
  · intro h
    exact ⟨h.to_normal.toIsAlgebraic, h.to_normal, h.to_isSeparable⟩
  · rintro ⟨_, hn, hs⟩
    exact { to_isSeparable := hs, to_normal := hn }

/-- Products apply the right factor first. -/
theorem galoisGroup_mul_apply {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (σ τ : L ≃ₐ[K] L) (x : L) :
    (σ * τ) x = σ (τ x) := rfl

/-- Every member of G fixes the specified image of K. -/
theorem galoisGroup_fixes_base {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (a : K) :
    σ (algebraMap K L a) = algebraMap K L a := σ.commutes a

/-- The lower scalar map is the restriction of the chosen base map. -/
theorem intermediate_baseMap_coe {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) (a : K) :
    ((algebraMap K M a : M) : L) = algebraMap K L a := rfl

/-- The upper scalar map is literal inclusion. -/
theorem intermediate_topMap_apply {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) (x : M) :
    algebraMap M L x = (x : L) := rfl

/-- The inclusion scalar structures form the usual field tower. -/
theorem intermediate_scalarTower {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) :
    IsScalarTower K M L := inferInstance

/-- Inclusions between intermediate fields preserve the ambient element. -/
theorem intermediate_inclusion_coe {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {M N : IntermediateField K L} (h : M ≤ N) (x : M) :
    ((IntermediateField.inclusion h x : N) : L) = (x : L) := rfl

/-- G_M is exactly the subgroup fixing every element of M. -/
theorem mem_fixingSubgroup {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) (σ : L ≃ₐ[K] L) :
    σ ∈ M.fixingSubgroup ↔ ∀ x ∈ M, σ x = x := IntermediateField.mem_fixingSubgroup_iff M σ

/-- The intrinsic automorphism and the subgroup element have the same action. -/
theorem fixingSubgroupEquiv_apply {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) (σ : M.fixingSubgroup) (x : L) :
    M.fixingSubgroupEquiv σ x = (σ : L ≃ₐ[K] L) x := rfl

/-- The fixed field has precisely the source fixed-element set. -/
theorem mem_fixedField {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L)) (x : L) :
    x ∈ IntermediateField.fixedField H ↔ ∀ σ ∈ H, σ x = x := IntermediateField.mem_fixedField_iff H x

/-- The fixed field contains the specified image of K. -/
theorem fixedField_contains_base {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L)) (a : K) :
    algebraMap K L a ∈ IntermediateField.fixedField H := (IntermediateField.fixedField H).algebraMap_mem a

/-- The fixed-element set is closed under all field operations (even inverse at zero). -/
theorem fixedField_operations {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L)) :
    (0 : L) ∈ IntermediateField.fixedField H ∧
    (1 : L) ∈ IntermediateField.fixedField H ∧
    (∀ x y : L, x ∈ IntermediateField.fixedField H → y ∈ IntermediateField.fixedField H →
      x + y ∈ IntermediateField.fixedField H) ∧
    (∀ x : L, x ∈ IntermediateField.fixedField H → -x ∈ IntermediateField.fixedField H) ∧
    (∀ x y : L, x ∈ IntermediateField.fixedField H → y ∈ IntermediateField.fixedField H →
      x * y ∈ IntermediateField.fixedField H) ∧
    (∀ x : L, x ∈ IntermediateField.fixedField H → x⁻¹ ∈ IntermediateField.fixedField H) := by
  let F := IntermediateField.fixedField H
  exact ⟨F.zero_mem, F.one_mem, fun _ _ hx hy => F.add_mem hx hy,
    fun _ hx => F.neg_mem hx, fun _ _ hx hy => F.mul_mem hx hy,
    fun _ hx => F.inv_mem hx⟩

/-- K(S) is the least intermediate field containing S. -/
theorem generatedField_le_iff {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (S : Set L) (M : IntermediateField K L) :
    IntermediateField.adjoin K S ≤ M ↔ S ⊆ (M : Set L) := IntermediateField.adjoin_le_iff

/-- Membership in the embedded image is actual image membership. -/
theorem mem_embeddedField {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L) (x : L) :
    x ∈ i.fieldRange ↔ ∃ a : E, i a = x := Iff.rfl

/-- Transport to the image followed by inclusion is the original embedding. -/
theorem embeddingEquiv_coe {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {E : Type w} [Field E] [Algebra K E] (i : E →ₐ[K] L) (a : E) :
    ((i.equivFieldRange a : i.fieldRange) : L) = i a := rfl

end AdvancedFieldTheory
