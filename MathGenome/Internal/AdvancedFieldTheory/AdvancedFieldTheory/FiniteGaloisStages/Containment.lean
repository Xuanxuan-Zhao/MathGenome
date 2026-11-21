import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteGaloisStages.Containment
import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# Finite Galois stages containing finite sets

FT-F03. Adjoining the given finite set gives a finite extension because the
ambient Galois extension is algebraic. Its normal closure inside the given
ambient field is still finite and is Galois over the base. It contains the
adjoined field, so it contains the original set. Mathlib packages this
construction as `FiniteGaloisIntermediateField.adjoin`.
-/

universe u v

namespace AdvancedFieldTheory

/-- A finite subset of a Galois extension is contained in a finite Galois
intermediate field, including when the subset is empty. -/
theorem exists_finite_galois_containing
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (S : Set L) (hS : S.Finite) :
    ∃ E : IntermediateField K L,
      S ⊆ (E : Set L) ∧ FiniteDimensional K E ∧ IsGalois K E := by
  let : Finite S := hS.to_subtype
  let E := FiniteGaloisIntermediateField.adjoin K S
  exact ⟨E.toIntermediateField, FiniteGaloisIntermediateField.subset_adjoin K S,
    E.finiteDimensional, E.isGalois⟩

end AdvancedFieldTheory
