import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.InverseLimit.Profiniteness
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
Independent specification of the subgroup index assertion in FT-C06,
notes/003/advanced-field-theory.tex:780–785, 799–807.
The topology is the canonical Krull topology on the actual automorphism group.
`H.FiniteIndex` means that the set of left cosets is finite; it does not
require normality. Closedness is required only for the converse implication.
-/

universe u v

namespace Specs.AdvancedFieldTheory

/-- Every open subgroup is closed and has finitely many left cosets. -/
def open_subgroup_isClosed_and_finiteIndex_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)),
    IsOpen (H : Set (L ≃ₐ[K] L)) →
      IsClosed (H : Set (L ≃ₐ[K] L)) ∧ H.FiniteIndex

/-- A closed subgroup is open exactly when it has finite index. -/
def closed_subgroup_isOpen_iff_finiteIndex_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)),
    IsClosed (H : Set (L ≃ₐ[K] L)) →
      (IsOpen (H : Set (L ≃ₐ[K] L)) ↔ H.FiniteIndex)

end Specs.AdvancedFieldTheory
