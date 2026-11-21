import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
Independent statement of Proposition F02, “The upper part of a Galois tower”,
notes/003/advanced-field-theory.tex:178–194.

The algebra structures on an intermediate field and on the upper extension
are the canonical inclusions. There is no finite-degree hypothesis and no
normality hypothesis on the lower extension.
-/

universe u v

namespace Specs.AdvancedFieldTheory

/-- The lower extension is algebraic and separable; the upper extension is
algebraic, normal and separable. -/
def galois_tower_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L),
    Algebra.IsAlgebraic K M ∧ Algebra.IsSeparable K M ∧
      Algebra.IsAlgebraic M L ∧ Normal M L ∧ Algebra.IsSeparable M L

end Specs.AdvancedFieldTheory
