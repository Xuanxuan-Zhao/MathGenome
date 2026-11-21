import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.InverseLimit.CompatibleTuples

/-!
Independent specification of FT-T05 (notes/003/advanced-field-theory.tex:508–542).
The limit is the literal compatible-tuple group from FT-T04. All stages and
scalar maps are those of the specified ambient extension. No topology or
surjectivity assumption on the canonical map is imposed.
-/

universe u v
noncomputable section
set_option linter.checkUnivs false
namespace Specs.AdvancedFieldTheory

/-- View a finite-stage group element as its underlying algebra automorphism. -/
def finiteStageAutomorphism {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (E : finiteGaloisStage_value K L)
    (σ : finiteStageGroup_value E) : E.val ≃ₐ[K] E.val := σ

/-- The canonical homomorphism has the actual restrictions as its coordinates. -/
def canonicalRestriction_type :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (L ≃ₐ[K] L) →* compatibleTuples_value K L

def canonicalRestriction_value : canonicalRestriction_type.{u, v} :=
  fun K L _ _ _ =>
  { toFun := fun σ => ⟨fun E => restriction_value E.val σ, by
      intro E F h
      let : Algebra E.val F.val := (IntermediateField.inclusion h).toAlgebra
      let : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
      let : IsScalarTower E.val F.val L := IsScalarTower.of_algebraMap_eq' rfl
      exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E.val F.val σ).symm⟩
    map_one' := Subtype.ext (funext fun E => map_one (restriction_value E.val))
    map_mul' := fun σ τ =>
      Subtype.ext (funext fun E => map_mul (restriction_value E.val) σ τ) }

def canonicalRestriction_projection_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : finiteGaloisStage_value K L),
    (compatibleTupleProjection_value E).toMonoidHom.comp (canonicalRestriction_value K L) =
      restriction_value E.val

/-- Every compatible tuple glues to exactly one actual K-automorphism of L. -/
def compatibleTuple_gluing_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (τ : compatibleTuples_value K L),
    ∃! σ : L ≃ₐ[K] L,
      ∀ (E : finiteGaloisStage_value K L) (x : E.val),
        σ (x : L) = ((finiteStageAutomorphism E (τ.val E)) x : L)

/-- A simultaneous gluing function, with its coordinate rule and both inverse laws. -/
def canonicalRestriction_inverse_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    ∃ glue : compatibleTuples_value K L → (L ≃ₐ[K] L),
      (∀ (τ : compatibleTuples_value K L) (E : finiteGaloisStage_value K L) (x : E.val),
        glue τ (x : L) = ((finiteStageAutomorphism E (τ.val E)) x : L)) ∧
      Function.LeftInverse glue (canonicalRestriction_value K L) ∧
      Function.RightInverse glue (canonicalRestriction_value K L)

def canonicalRestriction_bijective_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    Function.Bijective (canonicalRestriction_value K L)

/-- The group isomorphism is uniquely determined by the given canonical homomorphism. -/
def canonicalRestriction_isomorphism_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    ∃! e : (L ≃ₐ[K] L) ≃* compatibleTuples_value K L,
      e.toMonoidHom = canonicalRestriction_value K L

def compatibleTupleProjection_surjective_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (E : finiteGaloisStage_value K L),
    Function.Surjective (compatibleTupleProjection_value E)

end Specs.AdvancedFieldTheory
