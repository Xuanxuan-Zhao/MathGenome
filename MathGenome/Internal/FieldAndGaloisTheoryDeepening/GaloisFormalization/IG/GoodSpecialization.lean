import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.GoodSpecialization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.SpecializationRootMatching
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.SpecializationDecomposition

open scoped Polynomial

namespace GaloisFormalization.IG

open SpecializationData SpecializationRootMatching SpecializationDecomposition

theorem goodSpecialization : Specs.GaloisFormalization.IG.GoodSpecialization := by
  intro k _ ℓ _ _ a f hf L _ _ _ _ hmonic hsep
  obtain ⟨i, hroots⟩ := existsRootMatchingEmbedding ℓ a f hf L hmonic hsep
  obtain ⟨hparameter, hvalues⟩ := normalizedValueGroup i
  obtain ⟨d, hreduces⟩ := decompositionEquivalence f hf hmonic hsep i hroots
  refine ⟨i, hroots, hparameter, hvalues,
    residueFieldEquivalence f hf hmonic hsep i hroots, d, hreduces,
    d.toMonoidHom.ker_eq_bot_iff.mpr d.injective, ?_, ?_⟩
  · exact Subtype.val_injective.comp d.symm.injective
  · rw [MonoidHom.range_comp, d.symm.toMonoidHom.range_eq_top_of_surjective d.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]

theorem goodSpecializationConjugacy : Specs.GaloisFormalization.IG.GoodSpecializationConjugacy := by
  intro k _ ℓ _ _ a f hf L _ _ _ _ hmonic hsep i j
  let := substitutionAlgebra ℓ a
  have hrange : j.fieldRange = i.fieldRange :=
    (pointEmbeddingRoots ℓ a f hf L hmonic hsep j).2.2.trans
      (pointEmbeddingRoots ℓ a f hf L hmonic hsep i).2.2.symm
  let σ : L ≃ₐ[RatFunc k] L :=
    (j.equivFieldRange.trans (IntermediateField.equivOfEq hrange)).trans i.equivFieldRange.symm
  have hσ (x : L) : j x = i (σ x) := by
    change _ = (i.equivFieldRange (σ x) : LaurentSeries ℓ)
    dsimp only [σ, AlgEquiv.trans_apply]
    rw [AlgEquiv.apply_symm_apply]
    rfl
  refine ⟨σ, hσ, ?_⟩
  have horder (x : L) : inducedOrder j.toRingHom x = inducedOrder i.toRingHom (σ x) :=
    congrArg (fun s : LaurentSeries ℓ => s.orderTop) (hσ x)
  have hconj (τ : L ≃ₐ[RatFunc k] L) (x : L) :
      MulAut.conj σ τ (σ x) = σ (τ x) := by
    rw [MulAut.conj_apply]
    change σ (τ (σ.symm (σ x))) = _
    rw [AlgEquiv.symm_apply_apply]
  have hmem (τ : L ≃ₐ[RatFunc k] L) :
      τ ∈ decompositionGroup j ↔ MulAut.conj σ τ ∈ decompositionGroup i := by
    constructor
    · intro h y hy
      obtain ⟨x, rfl⟩ := σ.surjective y
      change inducedOrder i.toRingHom (MulAut.conj σ τ (σ x)) = _
      rw [hconj, ← horder (τ x), ← horder x]
      exact h x ((map_ne_zero σ).mp hy)
    · intro h x hx
      change inducedOrder j.toRingHom (τ x) = inducedOrder j.toRingHom x
      rw [horder (τ x), horder x, ← hconj]
      exact h (σ x) ((map_ne_zero σ).mpr hx)
  ext τ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact (hmem ρ).mp hρ
  · intro hτ
    refine ⟨(MulAut.conj σ).symm τ, (hmem _).mpr ?_, (MulAut.conj σ).apply_symm_apply τ⟩
    rwa [MulEquiv.apply_symm_apply]

end GaloisFormalization.IG
