import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.GeometricGaloisGroup
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.RationalConstantFields
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.BaseChange.RestrictionIsomorphism

namespace GaloisFormalization.IG

open IntermediateField

/-- The base field is relatively algebraically closed in the realization. -/
abbrev IsRegularOver := @Specs.isRegularOver

/-- The restriction homomorphism from the geometric to the arithmetic group. -/
noncomputable abbrev geometricRestriction := @Specs.geometricRestriction

private theorem range_restrictScalarsHom_eq_fixingSubgroup
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {I L : IntermediateField K Ω} (h : I ≤ L) :
    letI : Algebra I L := (inclusion h).toAlgebra
    letI : IsScalarTower K I L := IsScalarTower.of_algebraMap_eq' rfl
    (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[I] L) →* (L ≃ₐ[K] L)).range =
      (restrict h).fixingSubgroup := by
  let : Algebra I L := (inclusion h).toAlgebra
  let : IsScalarTower K I L := IsScalarTower.of_algebraMap_eq' rfl
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).2
    rintro _ ⟨a, rfl⟩
    exact τ.commutes a
  · intro hσ
    refine ⟨{ σ.toRingEquiv with commutes' := fun a ↦ ?_ }, ?_⟩
    · exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ ⟨a, rfl⟩
    · exact AlgEquiv.ext (fun _ ↦ rfl)

/-- Restriction to the original realization is injective, has image the
group over the intersection, and is surjective exactly for regular realizations. -/
theorem geometricGaloisGroup : Specs.geometricGaloisGroup := by
  intro k Ω _ _ _ _ t ht _ L _ _
  let K := adjoin k {t}
  let B := rationalWithConstants t (algebraicClosure k Ω)
  let P := L ⊔ B
  let I := L ⊓ B
  let : Algebra B P := (inclusion le_sup_right).toAlgebra
  let : Algebra I L := (inclusion inf_le_left).toAlgebra
  let : IsScalarTower K I L := IsScalarTower.of_algebraMap_eq' rfl
  let ρ := geometricRestriction t L
  let ρ₀ := AdvancedFieldTheory.baseChangeRestriction L B
  let j : (L ≃ₐ[I] L) →* (L ≃ₐ[K] L) := AlgEquiv.restrictScalarsHom K
  have heval (σ : P ≃ₐ[B] P) (x : L) :
      ((ρ σ x : L) : Ω) = (σ ⟨(x : Ω), (le_sup_left : L ≤ P) x.property⟩ : Ω) := by
    let : Algebra L P := (inclusion le_sup_left).toAlgebra
    let : IsScalarTower K B P := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower K L P := IsScalarTower.of_algebraMap_eq' rfl
    exact congrArg Subtype.val ((σ.restrictScalars K).restrictNormal_commutes L x)
  have hρ : ρ = j.comp ρ₀ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    exact (heval σ x).trans (AdvancedFieldTheory.baseChangeRestriction_apply L B σ x).symm
  have hρinj : Function.Injective ρ := by
    rw [hρ]
    exact (AlgEquiv.restrictScalarsHom_injective K).comp
      (AdvancedFieldTheory.baseChangeRestriction_injective L B)
  have hρrange : ρ.range = j.range := by
    rw [hρ, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (AdvancedFieldTheory.baseChangeRestriction_surjective L B),
      Subgroup.map_top]
  have hintersection : Function.Surjective ρ ↔ I = ⊥ := by
    have hrestrict : restrict (inf_le_left : I ≤ L) = ⊥ ↔ I = ⊥ := by
      rw [← (lift_injective L).eq_iff, lift_restrict, lift_bot]
    rw [← MonoidHom.range_eq_top, hρrange,
      range_restrictScalarsHom_eq_fixingSubgroup (inf_le_left : I ≤ L),
      ← IsGalois.fixedField_eq_iff_fixingSubgroup_eq, IsGalois.fixedField_top, eq_comm]
    exact hrestrict
  refine ⟨heval, hρinj, hρrange, hintersection.trans ?_⟩
  rw [(constantIntersection k Ω t ht L).2.2]
  change (∀ x : L, IsAlgebraic k x → x ∈ Set.range (algebraMap k L)) ↔
    algebraicClosure k L = ⊥
  rw [eq_bot_iff]
  exact ⟨fun h x hx ↦ mem_bot.2 (h x (mem_algebraicClosure_iff.1 hx)),
    fun h x hx ↦ mem_bot.1 (h (mem_algebraicClosure_iff.2 hx))⟩

end GaloisFormalization.IG
