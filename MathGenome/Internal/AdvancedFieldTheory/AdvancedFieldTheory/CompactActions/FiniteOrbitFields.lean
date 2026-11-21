import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.CompactActions.FiniteOrbitFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
Finite orbit fields for C11 (notes/003/advanced-field-theory.tex, 957–994).
Open stabilizers and compactness make orbits finite. The restriction kernel
is the intersection of the stabilizers of the finite generator set, so the
restriction image is finite. Artin then supplies finite degree and the Galois
property, without any finite-degree assumption.
-/

universe u v
noncomputable section
open scoped Classical
namespace AdvancedFieldTheory.CompactActions

abbrev fixedBase := Specs.AdvancedFieldTheory.CompactActions.fixedBase
abbrev orbitGenerators := Specs.AdvancedFieldTheory.CompactActions.orbitGenerators
abbrev orbitField := Specs.AdvancedFieldTheory.CompactActions.orbitField

variable (G : Type u) (E : Type v) [Group G] [Field E] [MulSemiringAction G E]

lemma generator_stable (S : Finset E) (g : G) {x : E}
    (hx : x ∈ orbitGenerators G E S) : g • x ∈ orbitGenerators G E S := by
  obtain ⟨a, ha, h, rfl⟩ := hx
  exact ⟨a, ha, g * h, mul_smul g h a⟩

lemma orbitField_stable (S : Finset E) (g : G) (x : E)
    (hx : x ∈ orbitField G E S) : g • x ∈ orbitField G E S := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin _ _ (generator_stable G E S g hx)
  | algebraMap a =>
      change g • (a : E) ∈ orbitField G E S
      rw [a.property g]
      exact (orbitField G E S).algebraMap_mem a
  | add x y hx hy ihx ihy =>
      rw [smul_add]; exact (orbitField G E S).add_mem ihx ihy
  | inv x hx ih =>
      rw [smul_inv'']; exact (orbitField G E S).inv_mem ih
  | mul x y hx hy ihx ihy =>
      rw [smul_mul']; exact (orbitField G E S).mul_mem ihx ihy

instance orbitFieldAction (S : Finset E) : MulSemiringAction G (orbitField G E S) where
  smul g x := ⟨g • (x : E), orbitField_stable G E S g x x.property⟩
  one_smul x := Subtype.ext (one_smul G (x : E))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : E))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_one g := Subtype.ext (smul_one g)
  smul_add g x y := Subtype.ext (smul_add g (x : E) (y : E))
  smul_mul g x y := Subtype.ext (smul_mul' g (x : E) (y : E))

instance orbitFieldComm (S : Finset E) :
    SMulCommClass G (fixedBase G E) (orbitField G E S) where
  smul_comm g a x := by
    apply Subtype.ext
    change g • ((a : E) * (x : E)) = (a : E) * (g • (x : E))
    rw [smul_mul', a.property g]

/-- Restriction of the given action, with literal ambient evaluation. -/
def stageRestriction (S : Finset E) :
    G →* (orbitField G E S ≃ₐ[fixedBase G E] orbitField G E S) :=
  MulSemiringAction.toAlgAut G (fixedBase G E) (orbitField G E S)

@[simp] lemma stageRestriction_apply (S : Finset E) (g : G) (x : orbitField G E S) :
    (stageRestriction G E S g x : E) = g • (x : E) := rfl

lemma stageRestriction_eq_one_iff (S : Finset E) (g : G) :
    stageRestriction G E S g = 1 ↔ ∀ x ∈ orbitGenerators G E S, g • x = x := by
  constructor
  · intro h x hx
    have h' := congrArg (fun f : orbitField G E S ≃ₐ[fixedBase G E] orbitField G E S =>
      (f ⟨x, IntermediateField.subset_adjoin _ _ hx⟩ : E)) h
    exact h'
  · intro h
    apply AlgEquiv.coe_toAlgHom_injective
    apply IntermediateField.adjoin_algHom_ext
    intro x hx
    exact Subtype.ext (h x hx)

lemma stage_fixedField (S : Finset E) :
    IntermediateField.fixedField (stageRestriction G E S).range = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hfixed : ∀ g : G, g • (x : E) = (x : E) := by
    intro g
    have h := (IntermediateField.mem_fixedField_iff _ x).mp hx
      (stageRestriction G E S g) ⟨g, rfl⟩
    exact congrArg Subtype.val h
  rw [IntermediateField.mem_bot]
  exact ⟨⟨(x : E), hfixed⟩, Subtype.ext rfl⟩

section Compact
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (hOpen : ∀ a : E, IsOpen (MulAction.stabilizer G a : Set G))
include hOpen

theorem finite_orbits (a : E) : (MulAction.orbit G a).Finite := by
  let : Finite (G ⧸ MulAction.stabilizer G a) :=
    Subgroup.quotient_finite_of_isOpen _ (hOpen a)
  have : Finite (MulAction.orbit G a) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G a).symm
  exact Set.toFinite _

lemma orbitGenerators_finite (S : Finset E) : (orbitGenerators G E S).Finite := by
  have heq : orbitGenerators G E S = ⋃ a ∈ (S : Set E), MulAction.orbit G a := by
    ext y
    simp only [orbitGenerators, Specs.AdvancedFieldTheory.CompactActions.orbitGenerators,
      Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, MulAction.mem_orbit_iff]
    constructor <;> rintro ⟨x, hx, g, hg⟩ <;> exact ⟨x, hx, g, hg⟩
  rw [heq]
  exact S.finite_toSet.biUnion (fun a _ => finite_orbits G E hOpen a)

lemma stageRestriction_finite (S : Finset E) : Finite (stageRestriction G E S).range := by
  let T := orbitGenerators G E S
  have : Finite T := (orbitGenerators_finite G E hOpen S).to_subtype
  have hk : ((stageRestriction G E S).ker : Set G) =
      ⋂ x : T, (MulAction.stabilizer G (x : E) : Set G) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, stageRestriction_eq_one_iff, Set.mem_iInter,
      MulAction.mem_stabilizer_iff, Subtype.forall]
    rfl
  have hopen : IsOpen ((stageRestriction G E S).ker : Set G) := by
    rw [hk]
    exact isOpen_iInter_of_finite fun x => hOpen x
  let : Finite (G ⧸ (stageRestriction G E S).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).toEquiv

/-- Artin's finite fixed-field theorem is applied only after the image is proved finite. -/
theorem finiteOrbitStage (S : Finset E) :
    (orbitGenerators G E S).Finite ∧
    (∀ (g : G) (x : E), x ∈ orbitField G E S → g • x ∈ orbitField G E S) ∧
    ∃ ρ : G →* (orbitField G E S ≃ₐ[fixedBase G E] orbitField G E S),
      (∀ (g : G) (x : orbitField G E S), (ρ g x : E) = g • (x : E)) ∧
      Finite ρ.range ∧
      IntermediateField.fixedField ρ.range = ⊥ ∧
      FiniteDimensional (fixedBase G E) (orbitField G E S) ∧
      IsGalois (fixedBase G E) (orbitField G E S) ∧
      Function.Surjective ρ := by
  let ρ := stageRestriction G E S
  let H := ρ.range
  have : Finite H := stageRestriction_finite G E hOpen S
  have hf : IntermediateField.fixedField H = ⊥ := stage_fixedField G E S
  have hfd : FiniteDimensional (IntermediateField.fixedField H) (orbitField G E S) := by
    change FiniteDimensional (FixedPoints.subfield H (orbitField G E S)) (orbitField G E S)
    infer_instance
  rw [hf] at hfd
  let := hfd
  have : FiniteDimensional (fixedBase G E) (orbitField G E S) :=
    FiniteDimensional.trans (fixedBase G E) (⊥ : IntermediateField (fixedBase G E)
      (orbitField G E S)) (orbitField G E S)
  have hgal : IsGalois (IntermediateField.fixedField H) (orbitField G E S) :=
    IsGalois.of_fixed_field _ H
  rw [hf] at hgal
  have : IsGalois (fixedBase G E) (orbitField G E S) :=
    isGalois_iff_isGalois_bot.mp hgal
  have htop : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hf,
      IntermediateField.fixingSubgroup_bot]
  refine ⟨orbitGenerators_finite G E hOpen S, orbitField_stable G E S,
    ρ, stageRestriction_apply G E S, inferInstance, hf, inferInstance, inferInstance, ?_⟩
  intro σ
  have hσ : σ ∈ H := htop ▸ Subgroup.mem_top σ
  exact hσ

end Compact

lemma orbitField_mono {S T : Finset E} (h : S ⊆ T) :
    orbitField G E S ≤ orbitField G E T := by
  apply IntermediateField.adjoin.mono
  rintro y ⟨x, hx, g, rfl⟩
  exact ⟨x, h hx, g, rfl⟩

lemma self_mem_orbitField (S : Finset E) {x : E} (hx : x ∈ S) :
    x ∈ orbitField G E S :=
  IntermediateField.subset_adjoin _ _ ⟨x, hx, 1, one_smul G x⟩

theorem directed_cover_cofinal :
    (∀ S T : Finset E, orbitField G E S ≤ orbitField G E (S ∪ T) ∧
      orbitField G E T ≤ orbitField G E (S ∪ T)) ∧
    (∀ x : E, ∃ S : Finset E, x ∈ orbitField G E S) ∧
    (∀ M : IntermediateField (fixedBase G E) E,
      FiniteDimensional (fixedBase G E) M → IsGalois (fixedBase G E) M →
      ∃ S : Finset E, M ≤ orbitField G E S) ∧
    orbitField G E ∅ = ⊥ := by
  classical
  refine ⟨fun S T => ⟨orbitField_mono G E Finset.subset_union_left,
    orbitField_mono G E Finset.subset_union_right⟩,
    fun x => ⟨{x}, self_mem_orbitField G E {x} (Finset.mem_singleton_self x)⟩, ?_, ?_⟩
  · intro M hfd _
    let := hfd
    have hfg : M.FG := IntermediateField.essFiniteType_iff.mp inferInstance
    obtain ⟨S, hS⟩ := hfg
    refine ⟨S, ?_⟩
    rw [← hS, IntermediateField.adjoin_le_iff]
    exact fun x hx => self_mem_orbitField G E S hx
  · change IntermediateField.adjoin (fixedBase G E) (orbitGenerators G E ∅) = ⊥
    have he : orbitGenerators G E (∅ : Finset E) = ∅ := by
      ext x
      simp [orbitGenerators, Specs.AdvancedFieldTheory.CompactActions.orbitGenerators]
    rw [he, IntermediateField.adjoin_empty]

end AdvancedFieldTheory.CompactActions
