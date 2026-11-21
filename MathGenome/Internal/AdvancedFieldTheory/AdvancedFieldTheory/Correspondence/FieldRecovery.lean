import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.GaloisTowers
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.InitialDescriptions
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.FullFixedField
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.FieldRecovery

/-!
# Recovery of an arbitrary intermediate field

Proposition C02 of `notes/003/advanced-field-theory.tex`.
Closedness follows by intersecting the closed evaluation fibers. Recovery
uses the full fixed-field theorem over the new base field M, identifying
Gal(L/M) with the pointwise fixing subgroup inside Gal(L/K).
-/

universe u v

namespace AdvancedFieldTheory

/-- The subgroup fixing an arbitrary intermediate field is Krull closed. -/
theorem fixingSubgroup_isClosed
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L) :
    IsClosed (fixingSubgroup M : Set (GaloisGroup K L)) := by
  have hset : (fixingSubgroup M : Set (GaloisGroup K L)) =
      ⋂ x : M, {σ : GaloisGroup K L | σ (x : L) = (x : L)} := by
    ext σ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    change σ ∈ M.fixingSubgroup ↔ ∀ x : M, σ (x : L) = (x : L)
    rw [mem_fixingSubgroup M σ]
    exact ⟨fun h x => h x x.property, fun h x hx => h ⟨x, hx⟩⟩
  rw [hset]
  apply isClosed_iInter
  intro x
  let : TopologicalSpace L := ⊥
  let : DiscreteTopology L := ⟨rfl⟩
  have hc : Continuous (fun σ : GaloisGroup K L => σ (x : L)) :=
    (KrullTopology.continuous_iff_evaluations K L id).mp continuous_id (x : L)
  exact (isClosed_singleton : IsClosed {(x : L)}).preimage hc

/-- The fixed field of the subgroup fixing M is exactly M, even when M/K
is infinite or nonnormal. -/
theorem fixedField_fixingSubgroup
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L) :
    fixedField (fixingSubgroup M) = M := by
  have ht := galois_tower K L M
  let : IsGalois M L :=
    { to_normal := ht.2.2.2.1, to_isSeparable := ht.2.2.2.2 }
  apply le_antisymm
  · intro x hx
    have hfixed : x ∈ IntermediateField.fixedField
        (⊤ : Subgroup (GaloisGroup M L)) := by
      apply (mem_fixedField _ _).mpr
      intro σ _
      let τ : M.fixingSubgroup := M.fixingSubgroupEquiv.symm σ
      exact (mem_fixedField _ _).mp hx (τ : GaloisGroup K L) τ.property
    have hbot : x ∈ (⊥ : IntermediateField M L) := by
      rw [← full_fixedField_eq_bot M L]
      exact hfixed
    obtain ⟨m, hm⟩ := IntermediateField.mem_bot.mp hbot
    exact hm ▸ m.property
  · intro x hx
    exact (mem_fixedField _ _).mpr fun σ hσ => (mem_fixingSubgroup M σ).mp hσ x hx

end AdvancedFieldTheory
