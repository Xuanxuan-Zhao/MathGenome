import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.InverseLimit.Profiniteness
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.OpenFiniteIndex

/-!
# Open subgroups and finite index (FT-C06, subgroup assertion)

Compactness of the Krull topology makes the discrete space of cosets of an
open subgroup finite. Conversely, the quotient by a closed subgroup is T1;
when finite it is discrete, so the subgroup is open. Neither argument
requires the subgroup to be normal.
-/

universe u v

namespace AdvancedFieldTheory

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- Every open subgroup of the Galois group is closed and has finite index. -/
theorem open_subgroup_isClosed_and_finiteIndex (H : Subgroup (GaloisGroup K L))
    (hH : IsOpen (H : Set (GaloisGroup K L))) :
    IsClosed (H : Set (GaloisGroup K L)) ∧ H.FiniteIndex := by
  have : Finite (GaloisGroup K L ⧸ H) := H.quotient_finite_of_isOpen hH
  exact ⟨H.isClosed_of_isOpen hH, H.finiteIndex_of_finite_quotient⟩

/-- Closed subgroups of the Galois group are open exactly when of finite index. -/
theorem closed_subgroup_isOpen_iff_finiteIndex (H : Subgroup (GaloisGroup K L))
    (hH : IsClosed (H : Set (GaloisGroup K L))) :
    IsOpen (H : Set (GaloisGroup K L)) ↔ H.FiniteIndex := by
  constructor
  · intro hOpen
    exact (open_subgroup_isClosed_and_finiteIndex H hOpen).2
  · intro hIndex
    have : H.FiniteIndex := hIndex
    exact H.isOpen_of_isClosed_of_finiteIndex hH

end AdvancedFieldTheory
