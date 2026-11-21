import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.InverseLimit.CompatibleTuples
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.InverseLimit.Gluing

/-!
# Gluing compatible automorphisms (FT-T05)

A compatible tuple acts on an element through any finite Galois stage
containing it. Directedness proves independence of this choice. A common
stage proves preservation of the field operations. Gluing the inverse tuple
provides a two-sided inverse. Thus the canonical restriction homomorphism is
a group isomorphism, with surjective projections.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

open Specs.AdvancedFieldTheory (finiteStageAutomorphism)

abbrev canonicalRestriction : Specs.AdvancedFieldTheory.canonicalRestriction_type.{u, v} :=
  Specs.AdvancedFieldTheory.canonicalRestriction_value

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

theorem canonicalRestriction_projection (E : finiteGaloisStage K L) :
    (compatibleTupleProjection E).toMonoidHom.comp (canonicalRestriction K L) =
      restriction E.val := rfl

variable [IsGalois K L]

private theorem exists_stage (x : L) : ∃ E : finiteGaloisStage K L, x ∈ E.val := by
  obtain ⟨E, hfin, hgal, hx⟩ := exists_finite_galois_containing_element K L x
  exact ⟨⟨E, hfin, hgal⟩, hx⟩

private def chosenStage (x : L) : finiteGaloisStage K L := (exists_stage x).choose

private theorem mem_chosenStage (x : L) : x ∈ (chosenStage (K := K) x).val :=
  (exists_stage x).choose_spec

private def gluedFunction (τ : compatibleTuples K L) (x : L) : L :=
  (finiteStageAutomorphism (chosenStage (K := K) x)
    (τ.val (chosenStage (K := K) x))
      ⟨x, mem_chosenStage x⟩ : L)

omit [IsGalois K L] in
/-- Restricting a coordinate along an inclusion does not change its ambient value. -/
private theorem tuple_apply_of_le (τ : compatibleTuples K L)
    {E F : finiteGaloisStage K L} (h : E ≤ F) (x : E.val) :
    (finiteStageAutomorphism E (τ.val E) x : L) =
      (finiteStageAutomorphism F (τ.val F) (IntermediateField.inclusion h x) : L) := by
  rw [← τ.property E F h]
  exact stageRestriction_apply h (finiteStageAutomorphism F (τ.val F)) x

/-- The value used for gluing agrees with every stage containing the element. -/
private theorem gluedFunction_of_mem (τ : compatibleTuples K L)
    (E : finiteGaloisStage K L) (x : E.val) :
    gluedFunction τ (x : L) = ((finiteStageAutomorphism E (τ.val E)) x : L) := by
  obtain ⟨F, hchosen, hE⟩ := (finiteStageIndex K L).2 (chosenStage (K := K) (x : L)) E
  exact (tuple_apply_of_le τ hchosen ⟨x, mem_chosenStage (x : L)⟩).trans
    (tuple_apply_of_le τ hE x).symm

private theorem gluedFunction_mul (τ : compatibleTuples K L) (x y : L) :
    gluedFunction τ (x * y) = gluedFunction τ x * gluedFunction τ y := by
  obtain ⟨E, hx⟩ := exists_stage (K := K) x
  obtain ⟨F, hy⟩ := exists_stage (K := K) y
  obtain ⟨H, hE, hF⟩ := (finiteStageIndex K L).2 E F
  have hxH := hE hx
  have hyH := hF hy
  rw [gluedFunction_of_mem τ H ⟨x * y, H.val.mul_mem hxH hyH⟩,
    gluedFunction_of_mem τ H ⟨x, hxH⟩, gluedFunction_of_mem τ H ⟨y, hyH⟩]
  exact congrArg (fun z : H.val => (z : L)) (map_mul (finiteStageAutomorphism H (τ.val H)) ⟨x, hxH⟩ ⟨y, hyH⟩)

private theorem gluedFunction_add (τ : compatibleTuples K L) (x y : L) :
    gluedFunction τ (x + y) = gluedFunction τ x + gluedFunction τ y := by
  obtain ⟨E, hx⟩ := exists_stage (K := K) x
  obtain ⟨F, hy⟩ := exists_stage (K := K) y
  obtain ⟨H, hE, hF⟩ := (finiteStageIndex K L).2 E F
  have hxH := hE hx
  have hyH := hF hy
  rw [gluedFunction_of_mem τ H ⟨x + y, H.val.add_mem hxH hyH⟩,
    gluedFunction_of_mem τ H ⟨x, hxH⟩, gluedFunction_of_mem τ H ⟨y, hyH⟩]
  exact congrArg (fun z : H.val => (z : L)) (map_add (finiteStageAutomorphism H (τ.val H)) ⟨x, hxH⟩ ⟨y, hyH⟩)

private theorem gluedFunction_commutes (τ : compatibleTuples K L) (a : K) :
    gluedFunction τ (algebraMap K L a) = algebraMap K L a := by
  obtain ⟨E, hx⟩ := exists_stage (K := K) (algebraMap K L a)
  exact (gluedFunction_of_mem τ E (algebraMap K E.val a)).trans
    (congrArg (fun z : E.val => (z : L)) ((finiteStageAutomorphism E (τ.val E)).commutes a))

private theorem gluedFunction_left_inv (τ : compatibleTuples K L) (x : L) :
    gluedFunction τ⁻¹ (gluedFunction τ x) = x := by
  obtain ⟨E, hx⟩ := exists_stage (K := K) x
  rw [gluedFunction_of_mem τ E ⟨x, hx⟩,
    gluedFunction_of_mem τ⁻¹ E ((finiteStageAutomorphism E (τ.val E)) ⟨x, hx⟩)]
  exact congrArg (fun z : E.val => (z : L)) ((finiteStageAutomorphism E (τ.val E)).symm_apply_apply ⟨x, hx⟩)

private def gluedAutomorphism (τ : compatibleTuples K L) : GaloisGroup K L where
  toFun := gluedFunction τ
  invFun := gluedFunction τ⁻¹
  left_inv := gluedFunction_left_inv τ
  right_inv := by
    intro x
    simpa only [inv_inv] using gluedFunction_left_inv τ⁻¹ x
  map_mul' := gluedFunction_mul τ
  map_add' := gluedFunction_add τ
  commutes' := gluedFunction_commutes τ

/-- The restrictions determine an ambient automorphism uniquely. -/
private theorem automorphism_ext (σ σ' : GaloisGroup K L)
    (h : ∀ (E : finiteGaloisStage K L) (x : E.val), σ (x : L) = σ' (x : L)) :
    σ = σ' := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨E, hx⟩ := exists_stage (K := K) x
  exact h E ⟨x, hx⟩

theorem compatibleTuple_gluing (τ : compatibleTuples K L) :
    ∃! σ : GaloisGroup K L,
      ∀ (E : finiteGaloisStage K L) (x : E.val), σ (x : L) = ((finiteStageAutomorphism E (τ.val E)) x : L) := by
  refine ⟨gluedAutomorphism τ, gluedFunction_of_mem τ, ?_⟩
  intro σ hσ
  apply automorphism_ext
  intro E x
  exact (hσ E x).trans (gluedFunction_of_mem τ E x).symm

private theorem glue_restrict (σ : GaloisGroup K L) :
    gluedAutomorphism (canonicalRestriction K L σ) = σ := by
  apply automorphism_ext
  intro E x
  exact (gluedFunction_of_mem (canonicalRestriction K L σ) E x).trans
    (restriction_apply E.val σ x)

private theorem restrict_glue (τ : compatibleTuples K L) :
    canonicalRestriction K L (gluedAutomorphism τ) = τ := by
  apply Subtype.ext
  funext E
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact (restriction_apply E.val (gluedAutomorphism τ) x).trans
    (gluedFunction_of_mem τ E x)

theorem canonicalRestriction_inverse (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    ∃ glue : compatibleTuples K L → GaloisGroup K L,
      (∀ (τ : compatibleTuples K L) (E : finiteGaloisStage K L) (x : E.val),
        glue τ (x : L) = ((finiteStageAutomorphism E (τ.val E)) x : L)) ∧
      Function.LeftInverse glue (canonicalRestriction K L) ∧
      Function.RightInverse glue (canonicalRestriction K L) :=
  ⟨gluedAutomorphism, gluedFunction_of_mem, glue_restrict, restrict_glue⟩

theorem canonicalRestriction_bijective (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Function.Bijective (canonicalRestriction K L) :=
  ⟨Function.LeftInverse.injective glue_restrict, Function.RightInverse.surjective restrict_glue⟩

theorem canonicalRestriction_isomorphism (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    ∃! e : GaloisGroup K L ≃* compatibleTuples K L,
      e.toMonoidHom = canonicalRestriction K L := by
  refine ⟨MulEquiv.ofBijective (canonicalRestriction K L)
    (canonicalRestriction_bijective K L), rfl, ?_⟩
  intro e he
  apply MulEquiv.ext
  intro σ
  exact DFunLike.congr_fun he σ

theorem compatibleTupleProjection_surjective (E : finiteGaloisStage K L) :
    Function.Surjective (compatibleTupleProjection E) := by
  intro σ
  obtain ⟨τ, hτ⟩ := restriction_surjective E.val σ
  exact ⟨canonicalRestriction K L τ, hτ⟩

end AdvancedFieldTheory
