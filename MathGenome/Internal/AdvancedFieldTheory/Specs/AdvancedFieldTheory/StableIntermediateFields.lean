import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
Independent statement of Corollary F06 (Stable intermediate fields),
notes/003/advanced-field-theory.tex:289–307.

`M.map σ.toAlgHom` is the literal image intermediate field: its carrier is
`σ '' (M : Set L)`. Equality expresses both inclusions in setwise stability.
Neither the ambient extension nor the intermediate field is assumed finite.
-/

universe u v

namespace Specs.AdvancedFieldTheory

/-- An intermediate field of a Galois extension is Galois over the base
exactly when every ambient base-field automorphism preserves it as a set. -/
def isGalois_iff_stable_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L),
    IsGalois K M ↔ ∀ σ : L ≃ₐ[K] L, M.map σ.toAlgHom = M

end Specs.AdvancedFieldTheory
