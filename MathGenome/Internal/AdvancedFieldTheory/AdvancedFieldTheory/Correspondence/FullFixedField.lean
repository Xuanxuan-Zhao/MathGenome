import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteGaloisStages.Containment
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteIngredients.GaloisCorrespondence
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.RestrictionSystem
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.FullFixedField

/-!
# The full Galois group has fixed field the base field

Proposition C01. An element outside the base field lies in a finite Galois
stage. The finite fixed-field theorem supplies an automorphism moving it,
and surjective restriction lifts that automorphism to the ambient extension.
-/

universe u v

namespace AdvancedFieldTheory

/-- An element outside K is moved in a finite Galois intermediate field by
an automorphism that is the restriction of an ambient automorphism. -/
theorem exists_finite_galois_moving
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (x : L) (hx : x ∉ (⊥ : IntermediateField K L)) :
    ∃ E : IntermediateField K L,
      FiniteDimensional K E ∧ IsGalois K E ∧
      ∃ hx : x ∈ E, ∃ τ : stageGroup E, ∃ g : GaloisGroup K L,
        τ ⟨x, hx⟩ ≠ ⟨x, hx⟩ ∧
        (∀ y : E, (τ y : L) = g (y : L)) ∧ g x ≠ x := by
  classical
  obtain ⟨E, hsub, hfin, hGal⟩ :=
    exists_finite_galois_containing K L {x} (Set.finite_singleton x)
  let := hfin
  let := hGal
  have hxE : x ∈ E := hsub (Set.mem_singleton x)
  let xE : E := ⟨x, hxE⟩
  have hxbot : xE ∉ (⊥ : IntermediateField K E) := by
    intro h
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp h
    apply hx
    exact IntermediateField.mem_bot.mpr ⟨a, congrArg (fun y : E => (y : L)) ha⟩
  have hmoving : ∃ τ : stageGroup E, τ xE ≠ xE := by
    by_contra! h
    apply hxbot
    rw [← FiniteIngredients.finite_fixedField_top (K := K) (E := E)]
    exact (mem_fixedField _ _).mpr (fun τ _ => h τ)
  obtain ⟨τ, hτ⟩ := hmoving
  obtain ⟨g, hg⟩ := restriction_surjective E τ
  have hrestrict (y : E) : (τ y : L) = g (y : L) := by
    rw [← hg]
    exact restriction_apply E g y
  have hgmove : g x ≠ x := by
    intro h
    apply hτ
    apply Subtype.ext
    exact (hrestrict xE).trans h
  exact ⟨E, hfin, hGal, hxE, τ, g, hτ, hrestrict, hgmove⟩

/-- No element outside the specified base field is fixed by the full group. -/
theorem full_fixedField_eq_bot
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] :
    fixedField (⊤ : Subgroup (GaloisGroup K L)) = (⊥ : IntermediateField K L) := by
  apply le_antisymm _ bot_le
  intro x hx
  by_contra hbase
  obtain ⟨E, _, _, hxE, τ, g, _, _, hg⟩ :=
    exists_finite_galois_moving K L x hbase
  exact hg ((mem_fixedField _ _).mp hx g (Subgroup.mem_top g))

end AdvancedFieldTheory
