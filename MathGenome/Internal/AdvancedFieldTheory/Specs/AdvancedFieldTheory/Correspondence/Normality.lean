import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations
import Mathlib.FieldTheory.KrullTopology

/-!
Independent statements of FT-C08, notes/003/advanced-field-theory.tex:841–861.
The ambient extension is algebraic Galois and its automorphism group has
its canonical Krull topology. No finite-degree assumption is made in the
closed-subgroup equivalence. The final equivalence identifies precisely the
open normal subgroups with the stabilizers of finite Galois intermediate fields.
-/

universe u v

namespace Specs.AdvancedFieldTheory

/-- The field-to-subgroup direction of normality in the correspondence. -/
def fixingSubgroup_normal_iff_isGalois_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L),
    M.fixingSubgroup.Normal ↔ IsGalois K M

/-- Closedness is essential for recovering H from its fixed field. -/
def closed_normal_iff_fixedField_isGalois_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)),
    IsClosed (H : Set (L ≃ₐ[K] L)) →
      (H.Normal ↔ IsGalois K (IntermediateField.fixedField H))

/-- Open normal subgroups are exactly the pointwise stabilizers of finite
Galois intermediate extensions, with the literal stabilizer assignment. -/
def isOpen_and_normal_iff_exists_finite_galois_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)),
    (IsOpen (H : Set (L ≃ₐ[K] L)) ∧ H.Normal) ↔
      ∃ M : IntermediateField K L,
        FiniteDimensional K M ∧ IsGalois K M ∧ M.fixingSubgroup = H

end Specs.AdvancedFieldTheory
