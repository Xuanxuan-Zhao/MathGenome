import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations
import Mathlib.GroupTheory.Index

/-!
Independent specification of FT-C07, notes/003/advanced-field-theory.tex:808–837.
The quotient is the set of left cosets, defined for every subgroup, without
normality. All intermediate-field scalar maps are the canonical inclusions.
-/

universe u v

set_option linter.checkUnivs false

namespace Specs.AdvancedFieldTheory

/-- The restriction map exists even before imposing the Galois hypothesis. -/
def restrictionOnCosets_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L),
    ((L ≃ₐ[K] L) ⧸ M.fixingSubgroup) → (M →ₐ[K] L)

/-- The actual map induced by restriction on representatives. -/
def restrictionOnCosets_value : restrictionOnCosets_type :=
  fun {K} {L} _ _ _ M =>
    Quotient.lift (fun σ : L ≃ₐ[K] L => σ.toAlgHom.comp M.val) (by
      intro σ τ h
      apply AlgHom.ext
      intro m
      have hm := (IntermediateField.mem_fixingSubgroup_iff M (σ⁻¹ * τ)).mp
        (QuotientGroup.leftRel_apply.mp h) m m.property
      change σ.symm (τ (m : L)) = (m : L) at hm
      change σ (m : L) = τ (m : L)
      apply σ.symm.injective
      simpa only [σ.symm_apply_apply] using hm.symm)

def restrictionOnCosets_mk_apply_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (σ : L ≃ₐ[K] L) (m : M),
    restrictionOnCosets_value M (Quotient.mk _ σ) m = σ (m : L)

def restrictionOnCosets_bijective_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L), Function.Bijective (restrictionOnCosets_value M)

/-- A set equivalence, with its full evaluation rule on every representative. -/
def exists_cosetsEmbeddingsEquiv_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L),
    ∃ e : ((L ≃ₐ[K] L) ⧸ M.fixingSubgroup) ≃ (M →ₐ[K] L),
      ∀ (σ : L ≃ₐ[K] L) (m : M), e (Quotient.mk _ σ) m = σ (m : L)

/-- No normality of M/K, or finiteness of L/K, is required. -/
def fixingSubgroup_index_eq_finrank_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) [FiniteDimensional K M],
    M.fixingSubgroup.index = Module.finrank K M

end Specs.AdvancedFieldTheory
