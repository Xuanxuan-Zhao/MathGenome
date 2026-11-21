import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.InitialDescriptions
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.RestrictionContinuous

/-! Continuity of restriction to an arbitrary Galois intermediate extension
(FT-T03). Evaluation after restriction has the same singleton fibers as
ambient evaluation, and these evaluations determine the target Krull topology. -/

universe u v

namespace AdvancedFieldTheory.KrullTopology

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- Restriction is continuous for the intrinsic Krull topologies, including
when the Galois intermediate extension is infinite. -/
theorem restriction_continuous (M : IntermediateField K L) [IsGalois K M] :
    Continuous (restriction M) := by
  apply (continuous_iff_evaluations K M (restriction M)).mpr
  intro x
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  let : TopologicalSpace L := ⊥
  let : DiscreteTopology L := ⟨rfl⟩
  apply continuous_discrete_rng.mpr
  intro y
  have hfib : (fun σ => restriction M σ x) ⁻¹' {y} =
      (fun σ : L ≃ₐ[K] L => σ (x : L)) ⁻¹' {(y : L)} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← restriction_apply M σ x]
    exact Subtype.ext_iff
  rw [hfib]
  exact (isOpen_discrete _).preimage
    ((continuous_iff_evaluations K L (fun σ => σ)).mp continuous_id (x : L))

end AdvancedFieldTheory.KrullTopology
