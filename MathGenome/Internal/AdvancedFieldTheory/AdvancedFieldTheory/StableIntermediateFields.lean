import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.GaloisTowers
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.StableIntermediateFields

/-!
Corollary F06: stability under all ambient automorphisms characterizes
the Galois intermediate fields, including infinite intermediate extensions.
-/

universe u v

namespace AdvancedFieldTheory

/-- An intermediate field is Galois over the base if and only if its actual
image under every ambient base-field automorphism equals itself. -/
theorem isGalois_iff_stable
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L) :
    IsGalois K M ↔ ∀ σ : GaloisGroup K L, M.map σ.toAlgHom = M := by
  -- Normality is equivalent to equality with every automorphic image.
  -- The library criterion assumes only normality of the ambient extension.
  constructor
  · intro h
    exact IntermediateField.normal_iff_forall_map_eq'.mp h.to_normal
  · intro h
    exact isGalois_iff.mpr ⟨(galois_tower K L M).2.1,
      IntermediateField.normal_iff_forall_map_eq'.mpr h⟩

end AdvancedFieldTheory
