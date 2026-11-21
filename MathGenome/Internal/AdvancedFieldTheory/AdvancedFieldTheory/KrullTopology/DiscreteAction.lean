import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.InitialDescriptions
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.DiscreteAction

/-! Joint continuity of the natural action on discrete L, and its universal
property, as stated in FT-T03 and its proof. -/

universe u v w
noncomputable section

namespace AdvancedFieldTheory.KrullTopology

/-- The natural action is jointly continuous for the Krull topology and discrete L. -/
theorem continuous_action (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    letI : TopologicalSpace L := ⊥
    Continuous (fun p : (L ≃ₐ[K] L) × L => p.1 p.2) := by
  let : TopologicalSpace L := ⊥
  let : DiscreteTopology L := ⟨rfl⟩
  apply continuous_prod_of_discrete_right.mpr
  exact (continuous_iff_evaluations K L id).mp continuous_id

/-- Continuity of the induced action detects continuity of an arbitrary set map. -/
theorem continuous_of_continuous_action (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {X : Type w} [TopologicalSpace X] (u : X → (L ≃ₐ[K] L)) :
    letI : TopologicalSpace L := ⊥
    Continuous (fun p : X × L => u p.1 p.2) → Continuous u := by
  let : TopologicalSpace L := ⊥
  intro h
  apply (continuous_iff_evaluations K L u).mpr
  intro x
  exact h.comp (continuous_id.prodMk continuous_const)

end AdvancedFieldTheory.KrullTopology
