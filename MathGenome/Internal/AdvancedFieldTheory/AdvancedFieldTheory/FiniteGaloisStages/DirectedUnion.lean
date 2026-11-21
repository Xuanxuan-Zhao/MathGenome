import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteGaloisStages.Containment
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteGaloisStages.DirectedUnion

/-!
# The directed union of finite Galois stages

FT-F04A, the forward direction of Theorem F04. The base field gives a stage.
The actual compositum of two stages is finite, normal and separable, by the
corresponding Mathlib instances for intermediate-field suprema. Hence it is
a common upper bound. Applying FT-F03 to a singleton proves that every element
of the specified ambient field belongs to a stage, and thus the union is all L.
-/

universe u v

namespace AdvancedFieldTheory

theorem finite_galois_bot
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] :
    FiniteDimensional K (⊥ : IntermediateField K L) ∧
      IsGalois K (⊥ : IntermediateField K L) := by
  exact ⟨inferInstance, inferInstance⟩

theorem finite_galois_intermediateFields_nonempty
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] :
    {E : IntermediateField K L | FiniteDimensional K E ∧ IsGalois K E}.Nonempty := by
  exact ⟨⊥, finite_galois_bot K L⟩

/-- The literal compositum inside L is again finite Galois over K. -/
theorem finite_galois_compositum
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (E₁ E₂ : IntermediateField K L)
    (h₁ : FiniteDimensional K E₁ ∧ IsGalois K E₁)
    (h₂ : FiniteDimensional K E₂ ∧ IsGalois K E₂) :
    FiniteDimensional K (E₁ ⊔ E₂ : IntermediateField K L) ∧
      IsGalois K (E₁ ⊔ E₂ : IntermediateField K L) := by
  let := h₁.1
  let := h₁.2
  let := h₂.1
  let := h₂.2
  exact ⟨inferInstance, inferInstance⟩

theorem finite_galois_intermediateFields_directed
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] :
    DirectedOn (· ≤ ·)
      {E : IntermediateField K L | FiniteDimensional K E ∧ IsGalois K E} := by
  intro E₁ h₁ E₂ h₂
  exact ⟨E₁ ⊔ E₂, finite_galois_compositum K L E₁ E₂ h₁ h₂,
    le_sup_left, le_sup_right⟩

theorem exists_finite_galois_containing_element
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (x : L) :
    ∃ E : IntermediateField K L,
      FiniteDimensional K E ∧ IsGalois K E ∧ x ∈ E := by
  obtain ⟨E, hE, hfin, hgal⟩ :=
    exists_finite_galois_containing K L {x} (Set.finite_singleton x)
  exact ⟨E, hfin, hgal, hE (Set.mem_singleton x)⟩

theorem finite_galois_intermediateFields_union
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] :
    (⋃ (E : IntermediateField K L) (_ : FiniteDimensional K E ∧ IsGalois K E),
      (E : Set L)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨E, hfin, hgal, hx⟩ := exists_finite_galois_containing_element K L x
  exact Set.mem_iUnion.mpr ⟨E, Set.mem_iUnion.mpr ⟨⟨hfin, hgal⟩, hx⟩⟩

end AdvancedFieldTheory
