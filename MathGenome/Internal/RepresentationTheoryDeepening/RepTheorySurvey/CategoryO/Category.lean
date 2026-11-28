import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.Category
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.UniversalEnveloping
import Batteries.Tactic.OpenPrivate

/-! The full subcategory of weight modules with finite generation and local finiteness. -/

noncomputable section

namespace RepTheorySurvey.CategoryO

open CategoryTheory Module UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.VermaModules
open scoped Classical ModuleCat.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g]

abbrev Setup := Specs.RepTheorySurvey.CategoryO.Setup
abbrev RootTriple := @Specs.RepTheorySurvey.CategoryO.RootTriple
abbrev restrictedRepresentation := @Specs.RepTheorySurvey.CategoryO.restrictedRepresentation
abbrev restrictedLieRingModule := @Specs.RepTheorySurvey.CategoryO.restrictedLieRingModule
abbrev restrictedLieModule := @Specs.RepTheorySurvey.CategoryO.restrictedLieModule
abbrev weightSpace := @Specs.RepTheorySurvey.CategoryO.weightSpace_value
abbrev orbit := @Specs.RepTheorySurvey.CategoryO.orbit_value
abbrev Q := @Specs.RepTheorySurvey.CategoryO.rootLattice_value
abbrev QPlus := @Specs.RepTheorySurvey.CategoryO.positiveRootCone_value
abbrev weightLE := @Specs.RepTheorySurvey.CategoryO.weightLE_value
abbrev objects := @Specs.RepTheorySurvey.CategoryO.objects_value
abbrev O := @Specs.RepTheorySurvey.CategoryO.category_value
abbrev character := @Specs.RepTheorySurvey.CategoryO.character_value
abbrev M := @Specs.RepTheorySurvey.CategoryO.verma_value
abbrev L := @Specs.RepTheorySurvey.CategoryO.simpleQuotient_value

open Specs.RepTheorySurvey.CategoryO (positiveCoordinates_value rootLieSpan_value)

theorem mem_weightSpace : Specs.RepTheorySurvey.CategoryO.mem_weightSpace_type.{u, v} := by
  intro g _ _ H V _ _ _ _ μ x
  let := restrictedLieRingModule V (g := g)
  let := restrictedLieModule V (g := g)
  change x ∈ LieModule.weightSpace V (μ : H → ℂ) ↔ ∀ h : H, ⁅(h : g), x⁆ = μ h • x
  simpa only [LieSubalgebra.coe_bracket_of_module] using LieModule.mem_weightSpace (μ : H → ℂ) x

theorem mem_orbit : Specs.RepTheorySurvey.CategoryO.mem_orbit_type.{u, v} := by
  intro g _ _ N V _ _ _ _ x y
  rfl

open private positive_submodule negative_submodule borel_submodule
  cartan_positive_disjoint negative_borel_isCompl
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules

theorem root_parts : Specs.RepTheorySurvey.CategoryO.root_parts_type.{u} := by
  intro g _ _ _ D
  exact ⟨positive_submodule D.cartan D.direction, negative_submodule D.cartan D.direction⟩

theorem finite_simple_roots : Specs.RepTheorySurvey.CategoryO.finite_simple_roots_type.{u} := by
  intro g _ _ _ D
  have h := _root_.LieAlgebrasAndRepresentations.RealRootSpace.cartan_isMaximalToral
    D.semisimple D.cartan
  have hfin := _root_.LieAlgebrasAndRepresentations.rootSet_finite D.cartan h.1
  exact (hfin.subset (fun _ hi => hi.1.1 : SerreRelations.simple D.cartan D.direction ⊆ _)).to_subtype

theorem cartan_borel : Specs.RepTheorySurvey.CategoryO.cartan_borel_type.{u} := by
  intro g _ _ _ D
  have h := _root_.LieAlgebrasAndRepresentations.RealRootSpace.cartan_isMaximalToral
    D.semisimple D.cartan
  exact ⟨(borel_submodule D.cartan D.direction D.semisimple h D.regular).1,
    cartan_positive_disjoint D.cartan D.direction D.semisimple h,
    negative_borel_isCompl D.cartan D.direction D.semisimple h D.regular⟩

theorem exists_triples : Specs.RepTheorySurvey.CategoryO.exists_triples_type.{u} := by
  intro g _ _ _ hss H _ φ
  have ht := _root_.LieAlgebrasAndRepresentations.RealRootSpace.cartan_isMaximalToral hss H
  have hex (i : SerreRelations.simple H φ) : Nonempty (RootTriple H i.val) := by
    obtain ⟨e, f, he, hf, he₀, hf₀, hef, hhe, hhf⟩ :=
      _root_.LieAlgebrasAndRepresentations.exists_root_triple hss H ht i.val i.property.1.1
    exact ⟨⟨e, f, he, hf, he₀, hf₀, hef, hhe, hhf⟩⟩
  exact ⟨fun i => Classical.choice (hex i)⟩

private theorem rootPart_eq_rootLieSpan (H : LieSubalgebra ℂ g) (φ : Direction H)
    (s : Set ℝ) (h₀ : 0 ∉ s) :
    rootPart H φ s =
      rootLieSpan_value H {α | α ∈ RootDecomposition.rootSet_value H ∧ φ α ∈ s} := by
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro x ⟨α, hα, hx⟩
    by_cases hr : α ∈ RootDecomposition.rootSet_value H
    · exact LieSubalgebra.subset_lieSpan ⟨α, ⟨hr, hα⟩, hx⟩
    · have hne : α ≠ 0 := fun h => h₀ (by simpa [h] using hα)
      change x ∈ _root_.LieAlgebrasAndRepresentations.rootSpace H α at hx
      rw [_root_.LieAlgebrasAndRepresentations.rootSpace_eq_bot_of_not_mem
        H α hne hr, Submodule.mem_bot] at hx
      subst x
      exact (rootLieSpan_value H _).zero_mem
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro x ⟨α, hα, hx⟩
    exact LieSubalgebra.subset_lieSpan ⟨α, hα.2, hx⟩

theorem direction_for_positive_system :
    Specs.RepTheorySurvey.CategoryO.direction_for_positive_system_type.{u, v} := by
  intro g _ _ _ H P I _ b hP hcoords
  let ℓ : RealRootSpace.E H →ₗ[ℝ] ℝ := b.constr ℝ (fun _ => 1)
  have hpos (x : RealRootSpace.E H) (hx : positiveCoordinates_value b x) : 0 < ℓ x := by
    obtain ⟨n, ⟨i, hi⟩, rfl⟩ := hx
    simp only [map_sum, map_smul, ℓ, Basis.constr_basis, smul_eq_mul, mul_one]
    exact Finset.sum_pos' (fun j _ => Nat.cast_nonneg (n j))
      ⟨i, Finset.mem_univ _, Nat.cast_pos.mpr hi⟩
  have signs (α : Module.Dual ℂ H) (ha : α ∈ RootDecomposition.rootSet_value H) :
      (α ∈ P → 0 < ℓ (RealRootSpace.rootRestriction H α)) ∧
      (α ∉ P → ℓ (RealRootSpace.rootRestriction H α) < 0) := by
    refine ⟨fun h => hpos _ ((hcoords α ha).1 h), fun h => ?_⟩
    simpa only [map_neg, neg_pos] using hpos _ ((hcoords α ha).2 h)
  have hregular : ∀ x ∈ RealRootSpace.realRoots H, ℓ x ≠ 0 := by
    rintro _ ⟨α, ha, rfl⟩
    by_cases h : α ∈ P
    · exact ne_of_gt ((signs α ha).1 h)
    · exact ne_of_lt ((signs α ha).2 h)
  obtain ⟨φ, hφ, hφeq⟩ := _root_.LieAlgebrasAndRepresentations.VermaModules.direction_from_real
    H ℓ hregular
  have hplus : SerreRelations.positive H φ = P := by
    ext α
    change (α ∈ RootDecomposition.rootSet_value H ∧ 0 < φ α) ↔ α ∈ P
    rw [hφeq]
    constructor
    · rintro ⟨ha, h⟩
      exact by_contradiction fun hn => (not_lt_of_gt ((signs α ha).2 hn)) h
    · exact fun h => ⟨hP h, (signs α (hP h)).1 h⟩
  have hminus : {α | α ∈ RootDecomposition.rootSet_value H ∧ φ α ∈ Set.Iio 0} =
      RootDecomposition.rootSet_value H \ P := by
    ext α
    change (α ∈ RootDecomposition.rootSet_value H ∧ φ α < 0) ↔
      α ∈ RootDecomposition.rootSet_value H ∧ α ∉ P
    rw [hφeq]
    exact ⟨fun ⟨ha, hn⟩ => ⟨ha, fun hp => (not_lt_of_gt ((signs α ha).1 hp)) hn⟩,
      fun ⟨ha, hn⟩ => ⟨ha, (signs α ha).2 hn⟩⟩
  have hnPlus : positive_value H φ = rootLieSpan_value H P := by
    rw [positive_value, rootPart_eq_rootLieSpan H φ _ (by simp)]
    exact congrArg (rootLieSpan_value H) hplus
  refine ⟨φ, hφ, hplus, ?_, hnPlus, ?_, ?_⟩
  · unfold SerreRelations.simple
    rw [hplus]
  · rw [negative_value, rootPart_eq_rootLieSpan H φ _ (by simp), hminus]
  · rw [borel_value, hnPlus]

open _root_.LieAlgebrasAndRepresentations (positiveRoots simpleRoots simpleRoots_basis
  simpleRoots_finite positive_nat_expansion positive_or_neg_positive)

theorem direction_for_real_positive_system :
    Specs.RepTheorySurvey.CategoryO.direction_for_real_positive_system_type.{u} := by
  intro g _ _ _ H d
  let := d.normedAddCommGroup
  let := d.innerProductSpace
  intro w hw
  let R := RealRootSpace.realRoots H
  have hR : _root_.LieAlgebrasAndRepresentations.IsRootSystem R := d.root_system
  let : Fintype (simpleRoots R w) := (simpleRoots_finite hR.toRootAxioms w).fintype
  obtain ⟨b, hb⟩ := simpleRoots_basis R hR w hw
  have hcoords (x : RealRootSpace.E H) (hx : x ∈ positiveRoots R w) :
      positiveCoordinates_value b x := by
    obtain ⟨c, hc⟩ := positive_nat_expansion hR.toRootAxioms w hx
    refine ⟨c, ?_, ?_⟩
    · by_contra! h
      have hz : c = 0 := Finsupp.ext fun i => Nat.eq_zero_of_le_zero (h i)
      rw [hz, map_zero] at hc
      exact hR.nonzero x hx.1 hc.symm
    · rw [← hc, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp only [hb, Nat.cast_smul_eq_nsmul]
  refine direction_for_positive_system H _ b (fun _ h => h.1) (fun α hα => ⟨?_, ?_⟩)
  · exact fun h => hcoords _ h.2
  · intro hn
    rcases positive_or_neg_positive hR.toRootAxioms hw ⟨α, hα, rfl⟩ with hp | hm
    · exact (hn ⟨hα, hp⟩).elim
    · exact hcoords _ hm

theorem character_unique : Specs.RepTheorySurvey.CategoryO.character_unique_type.{u} := by
  intro g _ _ _ D lam
  obtain ⟨χ, hχ, huniq⟩ := _root_.LieAlgebrasAndRepresentations.VermaModules.character_existsUnique
    D.semisimple D.cartan D.direction D.regular lam
  have h : ∃ ψ, IsWeightCharacter D.cartan D.direction lam ψ := ⟨χ, hχ⟩
  have hc : IsWeightCharacter D.cartan D.direction lam (character D lam) :=
    Classical.epsilon_spec h
  exact ⟨hc, fun ψ hψ => (huniq ψ hψ).trans (huniq _ hc).symm⟩

section Submodules

variable (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V]
  [IsScalarTower ℂ (U g) V] [LieRingModule g V] [LieModule ℂ g V]

/-- The same subspaces, with stability expressed using either the Lie generators
or the entire enveloping algebra. -/
private def submoduleEquiv (agree : ∀ (x : g) (m : V), (ι ℂ x) • m = ⁅x, m⁆) :
    Submodule (U g) V ≃o LieSubmodule ℂ g V where
  toFun S :=
    { S.restrictScalars ℂ with
      lie_mem := fun {x m} hm => agree x m ▸ S.smul_mem (ι ℂ x) hm }
  invFun S :=
    { S.toSubmodule with
      smul_mem' := fun a => by
        change ∀ m : V, m ∈ S → a • m ∈ S
        induction a using _root_.Shared.Lie.enveloping_induction ℂ g with
        | scalar c =>
          intro m hm
          rw [algebraMap_smul]
          exact S.smul_mem c hm
        | generator x =>
          intro m hm
          exact agree x m ▸ S.lie_mem hm
        | mul a b ha hb =>
          intro m hm
          rw [mul_smul]
          exact ha _ (hb _ hm)
        | add a b ha hb =>
          intro m hm
          rw [add_smul]
          exact S.add_mem (ha _ hm) (hb _ hm) }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := Iff.rfl

end Submodules

def submoduleOrderIso : Specs.RepTheorySurvey.CategoryO.submoduleOrderIso_type.{u, v} := by
  intro g _ _ V _ _ _ _
  letI := restrictedLieRingModule V (g := g)
  letI := restrictedLieModule V (g := g)
  exact submoduleEquiv V (fun _ _ => rfl)

theorem submodule_correspondence :
    Specs.RepTheorySurvey.CategoryO.submodule_correspondence_type.{u, v} := by
  refine ⟨@submoduleOrderIso, ?_⟩
  intro g _ _ V _ _ _ _ S x
  rfl

section HighestWeightModules

open VermaWeightsUniversal (inducedLieRingModule inducedLieModule)

local instance {H : LieSubalgebra ℂ g} {φ : Direction H} {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule g (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {H : LieSubalgebra ℂ g} {φ : Direction H} {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ g (induced_value H φ χ) := inducedLieModule H φ χ

variable [FiniteDimensional ℂ g] (D : Setup g) (lam : D.Weight)

local notation "V₀" => induced_value D.cartan D.direction (character D lam)
local notation "S₀" => SimpleHighestWeightQuotient.simpleQuotient_value D.cartan D.direction (character D lam)
local notation "π₀" => SimpleHighestWeightQuotient.quotientMap D.cartan D.direction (character D lam)

private theorem quotient_smul_ι (x : g) (m : L D lam) :
    (ι ℂ x) • m = (LieModule.toEnd ℂ g S₀ x) m := by
  change (UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ g S₀) (ι ℂ x)) m = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]

/-- The canonical map from the Verma module to its pinned quotient, as a left-module map. -/
def quotientMap : M D lam →ₗ[U g] L D lam :=
  { toFun := π₀
    map_add' := map_add π₀
    map_smul' := fun a => by
      let : Module (U g) S₀ := (L D lam).isModule
      change ∀ m : V₀, π₀ (a • m) = a • (π₀ m)
      induction a using _root_.Shared.Lie.enveloping_induction ℂ g with
      | scalar c =>
        intro m
        change π₀ ((algebraMap ℂ (U g) c) • (m : V₀)) =
          (UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ g S₀)
            (algebraMap ℂ (U g) c)) (π₀ m)
        rw [algebraMap_smul, AlgHom.commutes, Module.algebraMap_end_apply]
        exact (π₀).toLinearMap.map_smul c m
      | generator x =>
        intro m
        change π₀ ⁅x, m⁆ =
          (UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ g S₀) (ι ℂ x)) (π₀ m)
        rw [UniversalEnvelopingAlgebra.lift_ι_apply]
        exact (π₀).map_lie x m
      | mul a b ha hb =>
        intro m
        rw [mul_smul, ha, hb, mul_smul]
      | add a b ha hb =>
        intro m
        rw [add_smul, map_add, ha, hb, add_smul] }

theorem quotientMap_apply (x : M D lam) : quotientMap D lam x = π₀ x := rfl

theorem quotientMap_surjective : Function.Surjective (quotientMap D lam) :=
  LieSubmodule.Quotient.surjective_mk'
    (SimpleHighestWeightQuotient.maximalSubmodule_value D.cartan D.direction (character D lam))

theorem quotient_map : Specs.RepTheorySurvey.CategoryO.quotient_map_type.{u} := by
  refine ⟨@quotientMap, ?_⟩
  intro g _ _ _ D lam
  exact ⟨quotientMap_surjective D lam, quotientMap_apply D lam⟩

theorem simpleQuotient_simple : IsSimpleModule (U g) (L D lam) := by
  let ρ := LieModule.toEnd ℂ g S₀
  let : Module (U g) S₀ := _root_.Shared.Lie.actionModule ℂ g S₀
    (UniversalEnvelopingAlgebra.lift ℂ ρ)
  let : IsScalarTower ℂ (U g) S₀ :=
    _root_.Shared.Lie.action_tower ℂ g S₀ (UniversalEnvelopingAlgebra.lift ℂ ρ)
  have h := (_root_.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.simple_quotient
    D.semisimple D.cartan D.direction D.regular lam (character D lam) (character_unique D lam).1
    D.e (fun i => ⟨(D.triple i).e_mem, (D.triple i).e_ne_zero⟩)).1
  have hU : IsSimpleOrder (Submodule (U g) S₀) :=
    (submoduleEquiv S₀ (quotient_smul_ι D lam)).isSimpleOrder_iff.mpr h
  exact (isSimpleModule_iff (U g) S₀).mpr hU

end HighestWeightModules

end RepTheorySurvey.CategoryO
