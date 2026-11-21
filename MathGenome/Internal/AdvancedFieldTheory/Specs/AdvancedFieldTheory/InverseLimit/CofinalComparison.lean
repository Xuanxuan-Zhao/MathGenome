import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.InverseLimit.CompatibleTuples

/-!
Independent specification of FT-T07B, notes/003/advanced-field-theory.tex:
577–587 and 604–613. The subset is cofinal for inclusion only: it need not
be a chain or contain composita. Both limits have the product subspace topology
and coordinatewise group operations on the actual finite-stage Galois groups.
-/

universe u v
noncomputable section
set_option linter.checkUnivs false
namespace Specs.AdvancedFieldTheory

/-- The compatibility equations restricted to a subset of the stage index. -/
def cofinalTuplesSubgroup_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (S : Set (finiteGaloisStage_value K L)),
    Subgroup (∀ D : S, finiteStageGroup_value D.val)

def cofinalTuplesSubgroup_value : cofinalTuplesSubgroup_type.{u, v} :=
  fun {K} {L} [Field K] [Field L] [Algebra K L] S =>
  { carrier := {σ | ∀ (D D' : S) (h : D.val ≤ D'.val),
        finiteStageTransition_value h (σ D') = σ D}
    one_mem' := fun D D' h => map_one (finiteStageTransition_value h)
    mul_mem' := by
      intro σ τ hσ hτ D D' h
      exact (map_mul (finiteStageTransition_value h) (σ D') (τ D')).trans
        (congrArg₂ (· * ·) (hσ D D' h) (hτ D D' h))
    inv_mem' := by
      intro σ hσ D D' h
      exact (map_inv (finiteStageTransition_value h) (σ D')).trans
        (congrArg Inv.inv (hσ D D' h)) }

def cofinalTuples_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (S : Set (finiteGaloisStage_value K L)), Type v

abbrev cofinalTuples_value : cofinalTuples_type.{u, v} :=
  fun {K} {L} [Field K] [Field L] [Algebra K L] S => ↥(cofinalTuplesSubgroup_value S)

/-- The comparison is literally coordinate restriction. -/
def cofinalRestriction_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (S : Set (finiteGaloisStage_value K L)),
    ContinuousMonoidHom (compatibleTuples_value K L) (cofinalTuples_value S)

def cofinalRestriction_value : cofinalRestriction_type.{u, v} :=
  fun {K} {L} [Field K] [Field L] [Algebra K L] S =>
  { toFun := fun σ => ⟨fun D => σ.val D.val, fun D D' h => σ.property D.val D'.val h⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    continuous_toFun :=
      (continuous_pi (fun D => (continuous_apply D.val).comp continuous_subtype_val)).subtype_mk _ }

/-- Restriction is a unique topological group isomorphism. Its inverse has the
specified entry for every upper stage in S, hence is independent of all choices.
The equivalence includes two-sided inverse laws and continuity in both directions. -/
def cofinalComparison_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (S : Set (finiteGaloisStage_value K L)),
    (∀ E : finiteGaloisStage_value K L, ∃ D : S, E ≤ D.val) →
    ∃! e : compatibleTuples_value K L ≃ₜ* cofinalTuples_value S,
      (∀ σ, e σ = cofinalRestriction_value S σ) ∧
      (∀ (τ : cofinalTuples_value S) (E : finiteGaloisStage_value K L)
        (D : S) (h : E ≤ D.val),
        (e.symm τ).val E = finiteStageTransition_value h (τ.val D))

end Specs.AdvancedFieldTheory
