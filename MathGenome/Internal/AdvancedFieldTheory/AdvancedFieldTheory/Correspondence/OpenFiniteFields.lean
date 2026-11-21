import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.FiniteKernels
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.FieldRecovery
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.OpenFiniteFields

/-!
# Open fixing subgroups and finite intermediate fields

FT-C06A. An open fixing subgroup contains a finite Galois stage kernel.
Reversing this containment by fixed fields embeds the intermediate field
in that finite stage. The converse is the finite-field basis property
of the Krull topology.
-/

universe u v
open scoped Topology

namespace AdvancedFieldTheory

/-- No normality hypothesis on the intermediate field is needed. -/
theorem fixingSubgroup_isOpen_iff_finiteDimensional
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L) :
    IsOpen (fixingSubgroup M : Set (GaloisGroup K L)) ↔ FiniteDimensional K M := by
  constructor
  · intro hM
    obtain ⟨E, _, hE⟩ := (KrullTopology.finiteGaloisKernels_nhds_one K L).mem_iff.mp
      (hM.mem_nhds (fixingSubgroup M).one_mem)
    have hsub : E.toIntermediateField.fixingSubgroup ≤ M.fixingSubgroup := by
      rw [KrullTopology.finiteGaloisKernel_eq_fixingSubgroup] at hE
      exact fun _ hσ => hE hσ
    have hME : M ≤ E.toIntermediateField := by
      rw [← fixedField_fixingSubgroup K L M,
        ← fixedField_fixingSubgroup K L E.toIntermediateField]
      exact IntermediateField.fixedField_antitone hsub
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hME).toLinearMap
      (IntermediateField.inclusion_injective hME)
  · intro hM
    let : FiniteDimensional K M := hM
    exact IntermediateField.fixingSubgroup_isOpen M

end AdvancedFieldTheory
