import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.GaloisTowers

/-!
Proposition F02: the upper part of a Galois tower is Galois.
The lower extension need not be normal, and the extension may be infinite.
-/

universe u v

namespace AdvancedFieldTheory

/-- For a Galois extension `L/K` and any intermediate field `M`, the extension
`M/K` is algebraic and separable, and `L/M` is algebraic, normal and separable.
All scalar structures are the canonical intermediate-field inclusions. -/
theorem galois_tower (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [IsGalois K L] (M : IntermediateField K L) :
    Algebra.IsAlgebraic K M ∧ Algebra.IsSeparable K M ∧
      Algebra.IsAlgebraic M L ∧ Normal M L ∧ Algebra.IsSeparable M L := by
  have lower_separable : Algebra.IsSeparable K M :=
    Algebra.isSeparable_tower_bot_of_isSeparable K M L
  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  exact ⟨inferInstance, lower_separable, inferInstance, inferInstance, inferInstance⟩

end AdvancedFieldTheory
