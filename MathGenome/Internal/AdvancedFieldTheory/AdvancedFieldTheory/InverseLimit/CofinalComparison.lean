import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.InverseLimit.CompatibleTuples
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.InverseLimit.CofinalComparison

/-! # Cofinal comparison of the finite Galois inverse limits (FT-T07B)
Reconstruction restricts from any upper field in the cofinal subset. To compare
two choices we first take an upper bound in the full index and then use
cofinality. No closure condition is imposed on the subset.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

abbrev cofinalTuplesSubgroup : Specs.AdvancedFieldTheory.cofinalTuplesSubgroup_type.{u, v} :=
  Specs.AdvancedFieldTheory.cofinalTuplesSubgroup_value

abbrev cofinalTuples : Specs.AdvancedFieldTheory.cofinalTuples_type.{u, v} :=
  Specs.AdvancedFieldTheory.cofinalTuples_value

abbrev cofinalRestriction : Specs.AdvancedFieldTheory.cofinalRestriction_type.{u, v} :=
  Specs.AdvancedFieldTheory.cofinalRestriction_value

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- Independence of the upper field used to reconstruct a coordinate. -/
theorem cofinal_entry_independent
    (S : Set (finiteGaloisStage K L))
    (hS : ∀ E : finiteGaloisStage K L, ∃ D : S, E ≤ D.val)
    (τ : cofinalTuples S) (E : finiteGaloisStage K L)
    (D D' : S) (h : E ≤ D.val) (h' : E ≤ D'.val) :
    finiteStageTransition h (τ.val D) = finiteStageTransition h' (τ.val D') := by
  obtain ⟨H, hDH, hD'H⟩ := (finiteStageIndex K L).2 D.val D'.val
  obtain ⟨U, hHU⟩ := hS H
  have hDU : D.val ≤ U.val := hDH.trans hHU
  have hD'U : D'.val ≤ U.val := hD'H.trans hHU
  rw [← τ.property D U hDU, ← τ.property D' U hD'U]
  rw [← finiteStageTransition_laws.2.2 h hDU,
    ← finiteStageTransition_laws.2.2 h' hD'U]

/-- Coordinate restriction, with reconstruction by any upper cofinal field,
is the unique topological group isomorphism between the two limits. -/
theorem cofinalComparison
    (S : Set (finiteGaloisStage K L))
    (hS : ∀ E : finiteGaloisStage K L, ∃ D : S, E ≤ D.val) :
    ∃! e : compatibleTuples K L ≃ₜ* cofinalTuples S,
      (∀ σ, e σ = cofinalRestriction S σ) ∧
      (∀ (τ : cofinalTuples S) (E : finiteGaloisStage K L)
        (D : S) (h : E ≤ D.val),
        (e.symm τ).val E = finiteStageTransition h (τ.val D)) := by
  classical
  let upper : finiteGaloisStage K L → S := fun E => (hS E).choose
  have hupper (E : finiteGaloisStage K L) : E ≤ (upper E).val := (hS E).choose_spec
  let entry (τ : cofinalTuples S) (E : finiteGaloisStage K L) :=
    finiteStageTransition (hupper E) (τ.val (upper E))
  have entry_eq (τ : cofinalTuples S) (E : finiteGaloisStage K L)
      (D : S) (h : E ≤ D.val) :
      entry τ E = finiteStageTransition h (τ.val D) :=
    cofinal_entry_independent S hS τ E (upper E) D (hupper E) h
  have entry_compatible (τ : cofinalTuples S)
      (E F : finiteGaloisStage K L) (h : E ≤ F) :
      finiteStageTransition h (entry τ F) = entry τ E := by
    rw [entry_eq τ E (upper F) (h.trans (hupper F))]
    exact (finiteStageTransition_laws.2.2 h (hupper F) (τ.val (upper F))).symm
  let reconstruct : ContinuousMonoidHom (cofinalTuples S) (compatibleTuples K L) :=
    { toFun := fun τ => ⟨entry τ, entry_compatible τ⟩
      map_one' := by
        apply Subtype.ext
        funext E
        exact map_one (finiteStageTransition (hupper E))
      map_mul' := by
        intro τ υ
        apply Subtype.ext
        funext E
        exact map_mul (finiteStageTransition (hupper E)) (τ.val (upper E)) (υ.val (upper E))
      continuous_toFun :=
        (continuous_pi (fun E => (finiteStageTransition (hupper E)).continuous.comp
          ((continuous_apply (upper E)).comp continuous_subtype_val))).subtype_mk _ }
  have left_inv (σ : compatibleTuples K L) :
      reconstruct (cofinalRestriction S σ) = σ := by
    apply Subtype.ext
    funext E
    exact σ.property E (upper E).val (hupper E)
  have right_inv (τ : cofinalTuples S) :
      cofinalRestriction S (reconstruct τ) = τ := by
    apply Subtype.ext
    funext D
    exact (entry_eq τ D.val D (le_refl D.val)).trans
      (finiteStageTransition_laws.2.1 D.val (τ.val D))
  let e : compatibleTuples K L ≃ₜ* cofinalTuples S :=
    { toFun := cofinalRestriction S
      invFun := reconstruct
      left_inv := left_inv
      right_inv := right_inv
      map_mul' := (cofinalRestriction S).map_mul
      continuous_toFun := (cofinalRestriction S).continuous
      continuous_invFun := reconstruct.continuous }
  refine ⟨e, ⟨fun _ => rfl, ?_⟩, ?_⟩
  · intro τ E D h
    exact entry_eq τ E D h
  · intro e' he'
    apply ContinuousMulEquiv.ext
    intro σ
    exact he'.1 σ

end AdvancedFieldTheory
