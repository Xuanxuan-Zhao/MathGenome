import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteIngredients.SeparableSplittingField
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.GaloisTowers
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.BaseChange.GaloisExtensions

/-!
Galois base change in a common overfield (C10, Galoisness assertions).
We express the compositum over M as the supremum of root fields of the
K-minimal polynomials of elements of E, now regarded as polynomials over M.
Each root field is Galois by the separable splitting-field theorem. Suprema
of normal, separable intermediate fields are normal and separable, including
for infinite E/K and arbitrary M/K.
-/

universe u v

namespace AdvancedFieldTheory

open IntermediateField

/-- Base change preserves Galoisness, with no algebraicity assumption on M/K. -/
theorem galois_compositum_over_right
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (E M : IntermediateField K Ω) [IsGalois K E] :
    letI : Algebra M (E ⊔ M : IntermediateField K Ω) :=
      (IntermediateField.inclusion le_sup_right).toAlgebra
    IsGalois M (E ⊔ M : IntermediateField K Ω) := by
  let R : E → IntermediateField M Ω := fun x =>
    adjoin M (((minpoly K x).map (algebraMap K M)).rootSet Ω)
  have hR : ∀ x, IsGalois M (R x) := by
    intro x
    have hs : (((minpoly K x).map (algebraMap K M)).map
        (algebraMap M Ω)).Splits := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      exact (IsGalois.splits K x).of_algHom E.val
    exact (separable_rootField_finite_galois M Ω _
      (Polynomial.Separable.map (IsGalois.separable K x)) hs).2.2.2
  have hroots (x : E) :
      (((minpoly K x).map (algebraMap K M)).rootSet Ω) =
        E.val '' ((minpoly K x).rootSet E) := by
    rw [Polynomial.rootSet_map]
    exact ((IsGalois.splits K x).image_rootSet E.val).symm
  have heq : (⨆ x, R x) = extendScalars (le_sup_right : M ≤ E ⊔ M) := by
    apply le_antisymm
    · refine iSup_le fun x => adjoin_le_iff.mpr ?_
      rw [hroots]
      rintro _ ⟨y, _, rfl⟩
      exact (le_sup_left : E ≤ E ⊔ M) y.property
    · change E ⊔ M ≤ (⨆ x, R x).restrictScalars K
      apply sup_le
      · intro x hx
        let y : E := ⟨x, hx⟩
        apply (le_iSup R y)
        apply subset_adjoin
        rw [hroots]
        exact ⟨y, Polynomial.mem_rootSet.mpr
          ⟨minpoly.ne_zero (IsGalois.integral K y), minpoly.aeval K y⟩, rfl⟩
      · intro x hx
        exact (⨆ x, R x).algebraMap_mem ⟨x, hx⟩
  have : ∀ x, IsGalois M (R x) := hR
  have hgal : IsGalois M (⨆ x, R x : IntermediateField M Ω) := {}
  rw [heq] at hgal
  exact hgal

/-- The upper part of E/K above the literal intersection E ∩ M is Galois. -/
theorem galois_over_intersection
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (E M : IntermediateField K Ω) [IsGalois K E] :
    let : Algebra (E ⊓ M : IntermediateField K Ω) E :=
      (IntermediateField.inclusion inf_le_left).toAlgebra
    IsGalois (E ⊓ M : IntermediateField K Ω) E := by
  let : Algebra (E ⊓ M : IntermediateField K Ω) E :=
    (IntermediateField.inclusion inf_le_left).toAlgebra
  have : IsScalarTower K (E ⊓ M : IntermediateField K Ω) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact IsGalois.tower_top_of_isGalois K (E ⊓ M : IntermediateField K Ω) E

end AdvancedFieldTheory
