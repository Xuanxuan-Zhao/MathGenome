import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.RestrictionSystem
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteIngredients.GaloisCorrespondence
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.FiniteLayerFixedField

/-!
# Fixed fields on a finite layer

C03 of notes/003/advanced-field-theory.tex. The first equality holds even
without finiteness of E/K or the Galois condition on L/K. The recovery of
the restriction image uses the finite Galois correspondence in E/K.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Pulling the ambient fixed field back to E gives the fixed field of the
actual subgroup image under restriction. -/
theorem fixedField_comap_restriction
    (H : Subgroup (GaloisGroup K L)) (E : IntermediateField K L) [IsGalois K E] :
    (fixedField H).comap E.val = fixedField (H.map (restriction E)) := by
  ext x
  change ((x : L) ∈ IntermediateField.fixedField H) ↔
    x ∈ IntermediateField.fixedField (H.map (restriction E))
  rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_fixedField_iff]
  constructor
  · intro hx τ hτ
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hτ
    apply Subtype.ext
    exact (restriction_apply E σ x).trans (hx σ hσ)
  · intro hx σ hσ
    have h := hx (restriction E σ) (Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩)
    exact (restriction_apply E σ x).symm.trans (congrArg Subtype.val h)

/-- Inside L, the intersection L^H ∩ E is the canonical lift of E^{r_E(H)}. -/
theorem fixedField_inf_finiteLayer
    (H : Subgroup (GaloisGroup K L)) (E : IntermediateField K L) [IsGalois K E] :
    fixedField H ⊓ E = (fixedField (H.map (restriction E))).map E.val := by
  rw [← fixedField_comap_restriction H E]
  ext x
  constructor
  · rintro ⟨hx, hxE⟩
    exact ⟨⟨x, hxE⟩, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨hy, y.property⟩

/-- On a finite Galois layer the image of H is the full subgroup fixing
L^H ∩ E pointwise, with the intersection represented inside E. -/
theorem restriction_image_eq_fixingSubgroup [IsGalois K L]
    (H : Subgroup (GaloisGroup K L)) (E : IntermediateField K L)
    [FiniteDimensional K E] [IsGalois K E] :
    H.map (restriction E) = fixingSubgroup ((fixedField H).comap E.val) := by
  rw [fixedField_comap_restriction H E]
  exact (FiniteIngredients.finite_fixingSubgroup_fixedField (H.map (restriction E))).symm

end AdvancedFieldTheory
