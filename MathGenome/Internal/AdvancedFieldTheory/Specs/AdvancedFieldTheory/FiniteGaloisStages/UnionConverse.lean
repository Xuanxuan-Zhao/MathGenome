import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
The converse of Theorem F04, notes/003/advanced-field-theory.tex:215–249.
The stages are actual intermediate fields in the given ambient extension.
The index universe is unrestricted and the ambient extension need not be finite.
-/

universe u v w

namespace Specs.AdvancedFieldTheory

/-- An extension covered by a nonempty directed family of finite Galois
intermediate fields is Galois. -/
def isGalois_of_directed_union_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {ι : Type w} [Nonempty ι] (E : ι → IntermediateField K L),
    Directed (· ≤ ·) E →
    (∀ i, FiniteDimensional K (E i)) →
    (∀ i, IsGalois K (E i)) →
    (∀ x : L, ∃ i, x ∈ E i) →
    IsGalois K L

end Specs.AdvancedFieldTheory
