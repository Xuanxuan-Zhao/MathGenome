import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.CosetsEmbeddings
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.EmbeddingExtension
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.GaloisTowers
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteIngredients.SimpleEmbeddings

/-!
# Left cosets as embeddings

FT-C07: restriction identifies left cosets of the pointwise stabilizer with
embeddings of any intermediate field. Finite intermediates have index equal
to their degree, even when they are not normal over the base field.
-/

universe u v

namespace AdvancedFieldTheory

/-- Restriction descends to the set of left cosets of the fixing subgroup. -/
def restrictionOnCosets
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) :
    ((L ≃ₐ[K] L) ⧸ M.fixingSubgroup) → (M →ₐ[K] L) :=
  Specs.AdvancedFieldTheory.restrictionOnCosets_value M

@[simp]
theorem restrictionOnCosets_mk_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (σ : L ≃ₐ[K] L) (m : M) :
    restrictionOnCosets M (Quotient.mk _ σ) m = σ (m : L) := rfl

/-- Equal restrictions are exactly equal left cosets; every embedding extends. -/
theorem restrictionOnCosets_bijective
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) : Function.Bijective (restrictionOnCosets M) := by
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro σ τ h
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    apply (IntermediateField.mem_fixingSubgroup_iff M (σ⁻¹ * τ)).mpr
    intro x hx
    have hm := congrArg (fun f : M →ₐ[K] L => f ⟨x, hx⟩) h
    change σ x = τ x at hm
    change σ.symm (τ x) = x
    rw [← hm, σ.symm_apply_apply]
  · intro ι
    obtain ⟨σ, hσ⟩ := exists_automorphism_extending_embedding M ι
    refine ⟨Quotient.mk _ σ, ?_⟩
    exact AlgHom.ext hσ

/-- The quotient is a set quotient, with no normal-subgroup instance needed. -/
theorem exists_cosetsEmbeddingsEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) :
    ∃ e : ((L ≃ₐ[K] L) ⧸ M.fixingSubgroup) ≃ (M →ₐ[K] L),
      ∀ (σ : L ≃ₐ[K] L) (m : M), e (Quotient.mk _ σ) m = σ (m : L) := by
  exact ⟨Equiv.ofBijective (restrictionOnCosets M) (restrictionOnCosets_bijective M),
    fun _ _ => rfl⟩

/-- The number of left cosets equals the degree of every finite intermediate. -/
theorem fixingSubgroup_index_eq_finrank
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) [FiniteDimensional K M] :
    M.fixingSubgroup.index = Module.finrank K M := by
  haveI : Algebra.IsSeparable K M := (galois_tower K L M).2.1
  have hsplits : ∀ x : M, ((minpoly K x).map (algebraMap K L)).Splits := by
    intro x
    rw [← minpoly.algHom_eq M.val M.val.injective x]
    exact Normal.splits (inferInstance : Normal K L) (x : L)
  calc
    M.fixingSubgroup.index = Nat.card ((L ≃ₐ[K] L) ⧸ M.fixingSubgroup) :=
      M.fixingSubgroup.index_eq_card
    _ = Nat.card (M →ₐ[K] L) := Nat.card_congr
      (Equiv.ofBijective (restrictionOnCosets M) (restrictionOnCosets_bijective M))
    _ = Module.finrank K M := card_embeddings_of_splits K M L hsplits

end AdvancedFieldTheory
