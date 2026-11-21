import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
Independent statement for FT-F03, Proposition F03 in
`notes/003/advanced-field-theory.tex`, lines 197–214.
The finite set and the witnessing intermediate field belong to the specified
ambient extension. There is no nonemptiness or independence hypothesis on S.
-/

universe u v

namespace Specs.AdvancedFieldTheory

/-- Every finite subset of a Galois extension lies in a finite Galois
intermediate field of that same extension. -/
def exists_finite_galois_containing_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (S : Set L), S.Finite →
    ∃ E : IntermediateField K L,
      S ⊆ (E : Set L) ∧ FiniteDimensional K E ∧ IsGalois K E

end Specs.AdvancedFieldTheory
