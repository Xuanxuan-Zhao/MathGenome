import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.SimpleObjects
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightBounds
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightExactness
import Mathlib.Algebra.Category.ModuleCat.Simple

/-! Simple objects of the finite category O. -/

noncomputable section

open CategoryTheory Module UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations
open VermaModules (U highestVector_value envelopingMap)
open scoped Classical ModuleCat.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RepTheorySurvey.CategoryO

open Specs.RepTheorySurvey.CategoryO.SimpleObjects

universe u v w

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g)

private def cartanSubmodule (X : ModuleCat.{v} (U g)) (S : Submodule (U g) X) :
    letI := restrictedLieRingModule X (g := g)
    letI := restrictedLieModule X (g := g)
    LieSubmodule ℂ D.cartan X := by
  letI := restrictedLieRingModule X (g := g)
  letI := restrictedLieModule X (g := g)
  exact
    { S.restrictScalars ℂ with
      lie_mem := fun {h x} hx => S.smul_mem (ι ℂ (h : g)) hx }

private theorem submodule_mem_O (X : ModuleCat.{v} (U g)) (hX : objects D X)
    (S : Submodule (U g) X) (hS : S.FG) :
    objects D (ModuleCat.of (U g) S) := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  refine ⟨Module.Finite.of_fg hS, ?_, ?_⟩
  · exact (WeightExactness.stableSubspace (cartanSubmodule D X S) hX.2.1).1
  · intro x
    let := hX.2.2 (x : X)
    let f := (S.subtype.restrictScalars ℂ).restrict
      (p := orbit D.nPlus S x) (q := orbit D.nPlus X (x : X)) (by
        intro y hy
        obtain ⟨a, rfl⟩ := (mem_orbit D.nPlus S x y).mp hy
        exact (mem_orbit D.nPlus X (x : X) _).2 ⟨a, rfl⟩)
    exact FiniteDimensional.of_injective f (fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun y : orbit D.nPlus X (x : X) => (y : X)) h)))

private abbrev cyclicSpan (X : O.{u, v} D) (x : X.obj) := Submodule.span (U g) {x}

private abbrev cyclicObject (X : O.{u, v} D) (x : X.obj) : O.{u, v} D :=
  ⟨ModuleCat.of (U g) (cyclicSpan D X x),
    submodule_mem_O D X.obj X.property _ (Submodule.fg_span_singleton x)⟩

private def cyclicInclusion (X : O.{u, v} D) (x : X.obj) : cyclicObject D X x ⟶ X :=
  ObjectProperty.homMk (ModuleCat.ofHom (cyclicSpan D X x).subtype)

private theorem injective_of_mono {X Y : O.{u, v} D} (f : X ⟶ Y) [Mono f] :
    Function.Injective f.hom.hom := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro x hx
  have hle : cyclicSpan D X x ≤ f.hom.hom.ker :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hcomp : cyclicInclusion D X x ≫ f = 0 ≫ f := by
    rw [Limits.zero_comp]
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext y
    change f.hom.hom (y : X.obj) = 0
    exact hle y.property
  have heq := (cancel_mono f).1 hcomp
  let y : (cyclicObject D X x).obj := ⟨x, Submodule.mem_span_singleton_self x⟩
  have hzero := congrArg (fun k : cyclicObject D X x ⟶ X => k.hom.hom y) heq
  exact (Submodule.mem_bot (U g)).mpr hzero

/-- An O-object is simple exactly when it is simple as a left enveloping module. -/
theorem simple_iff_isSimpleModule : SimpleIffIsSimpleModuleType.{u, v} := by
  intro g _ _ _ D X
  constructor
  · intro h
    let := h
    have hne : (⊥ : Submodule (U g) X.obj) ≠ ⊤ := by
      intro heq
      apply CategoryTheory.id_nonzero X
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      exact (Submodule.mem_bot (U g)).mp (heq.symm ▸ Submodule.mem_top)
    rw [isSimpleModule_iff]
    let := nontrivial_of_ne _ _ hne
    constructor
    intro S
    by_cases hS : S = ⊥
    · exact Or.inl hS
    obtain ⟨x, hx, hxn⟩ := (S.ne_bot_iff).mp hS
    let f := cyclicInclusion D X x
    have : Mono f.hom := (ModuleCat.mono_iff_injective _).mpr
      (cyclicSpan D X x).subtype_injective
    have : Mono f := (objects D).ι.mono_of_mono_map (show Mono f.hom from inferInstance)
    have hf : f ≠ 0 := by
      intro hzero
      let y : (cyclicObject D X x).obj := ⟨x, Submodule.mem_span_singleton_self x⟩
      exact hxn (congrArg (fun k : cyclicObject D X x ⟶ X => k.hom.hom y) hzero)
    have : IsIso f := isIso_of_mono_of_nonzero hf
    have hsurj : Function.Surjective f.hom :=
      (ModuleCat.epi_iff_surjective f.hom).mp inferInstance
    refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨z, rfl⟩ := hsurj y
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) z.property
  · intro h
    let : Simple X.obj := (simple_iff_isSimpleModule' X.obj).mpr h
    refine ⟨fun {Y} f _ => ?_⟩
    have : Mono f.hom := (ModuleCat.mono_iff_injective _).mpr (injective_of_mono D f)
    have hz : f.hom = 0 ↔ f = 0 := ⟨fun e => ObjectProperty.hom_ext (objects D) e, fun e => by rw [e]; rfl⟩
    have hi : IsIso f ↔ IsIso f.hom := (isIso_iff_of_reflects_iso f (objects D).ι).symm
    exact hi.trans ((Simple.mono_isIso_iff_nonzero f.hom).trans (not_congr hz))

private theorem surjective_mem_O {X : ModuleCat.{v} (U g)} {Y : ModuleCat.{w} (U g)}
    (hX : objects D X) (f : X →ₗ[U g] Y) (hf : Function.Surjective f) : objects D Y := by
  let := hX.1
  let := restrictedLieRingModule Y (g := g)
  let := restrictedLieModule Y (g := g)
  let F := f.restrictScalars ℂ
  refine ⟨Module.Finite.of_surjective f hf, ?_, ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact WeightExactness.weightSpaces_independent (H := D.cartan) (X := Y)
    · have hmap (μ : D.Weight) :
          (weightSpace D.cartan X μ).map F ≤ weightSpace D.cartan Y μ := by
        rintro y ⟨x, hx, rfl⟩
        refine (mem_weightSpace D.cartan Y μ (f x)).mpr (fun h => ?_)
        calc
          (ι ℂ (h : g)) • f x = f ((ι ℂ (h : g)) • x) := (f.map_smul _ _).symm
          _ = f (μ h • x) := congrArg f ((mem_weightSpace D.cartan X μ x).mp hx h)
          _ = μ h • f x := F.map_smul (μ h) x
      have hspan : (⨆ μ, (weightSpace D.cartan X μ).map F) = ⊤ := by
        rw [← Submodule.map_iSup, hX.2.1.submodule_iSup_eq_top, Submodule.map_top]
        exact LinearMap.range_eq_top.mpr hf
      exact top_unique (hspan ▸ iSup_mono hmap)
  · intro y
    obtain ⟨x, rfl⟩ := hf y
    let := hX.2.2 x
    let q := F.restrict (p := orbit D.nPlus X x) (q := orbit D.nPlus Y (f x)) (by
      intro z hz
      obtain ⟨a, rfl⟩ := (mem_orbit D.nPlus X x z).mp hz
      exact (mem_orbit D.nPlus Y (f x) _).mpr ⟨a, (f.map_smul (envelopingMap D.nPlus.incl a) x).symm⟩)
    apply FiniteDimensional.of_surjective q
    intro z
    obtain ⟨a, ha⟩ := (mem_orbit D.nPlus Y (f x) z).mp z.property
    refine ⟨⟨envelopingMap D.nPlus.incl a • x, (mem_orbit D.nPlus X x _).mpr ⟨a, rfl⟩⟩, ?_⟩
    exact Subtype.ext ((f.map_smul _ x).trans ha)

section LieMaps

variable {V : Type v} {W : Type w}
  [AddCommGroup V] [Module ℂ V] [Module (U g) V] [IsScalarTower ℂ (U g) V]
  [AddCommGroup W] [Module ℂ W] [Module (U g) W] [IsScalarTower ℂ (U g) W]
  [LieRingModule g V] [LieModule ℂ g V] [LieRingModule g W] [LieModule ℂ g W]
  (agreeV : ∀ (a : g) (x : V), (ι ℂ a) • x = ⁅a, x⁆)
  (agreeW : ∀ (a : g) (x : W), (ι ℂ a) • x = ⁅a, x⁆)

private def lieHomOfEnvelopingHom (f : V →ₗ[U g] W) : V →ₗ⁅ℂ,g⁆ W :=
  { f.restrictScalars ℂ with
    map_lie' := fun {a x} => by
      change f ⁅a, x⁆ = ⁅a, f x⁆
      rw [← agreeV, ← agreeW, map_smul] }

private def envelopingHomOfLieHom (f : V →ₗ⁅ℂ,g⁆ W) : V →ₗ[U g] W where
  toFun := f
  map_add' := map_add f
  map_smul' a := by
    change ∀ x : V, f (a • x) = a • f x
    induction a using _root_.Shared.Lie.enveloping_induction ℂ g with
    | scalar c =>
      intro x
      rw [algebraMap_smul, algebraMap_smul]
      exact f.toLinearMap.map_smul c x
    | generator b => intro x; rw [agreeV, agreeW, f.map_lie]
    | mul a b ha hb => intro x; rw [mul_smul, ha, hb, mul_smul]
    | add a b ha hb => intro x; rw [add_smul, map_add, ha, hb, add_smul]

end LieMaps

section SimpleQuotients

open VermaModules (Direction borel_value induced_value envelopingMap)
open VermaWeightsUniversal (inducedLieRingModule inducedLieModule)
open SimpleHighestWeightQuotient (quotientHighestVector)

local instance {H : LieSubalgebra ℂ g} {φ : Direction H}
    {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule g (induced_value H φ χ) := inducedLieRingModule H φ χ
local instance {H : LieSubalgebra ℂ g} {φ : Direction H}
    {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ g (induced_value H φ χ) := inducedLieModule H φ χ

open private quotient_smul_ι from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.Category

private abbrev QuotientCarrier (lam : D.Weight) :=
  SimpleHighestWeightQuotient.simpleQuotient_value D.cartan D.direction (character D lam)

local instance (lam : D.Weight) : Module (U g) (QuotientCarrier D lam) := (L D lam).isModule

local instance (lam : D.Weight) : IsScalarTower ℂ (U g) (QuotientCarrier D lam) :=
  _root_.Shared.Lie.action_tower ℂ g _ (lift ℂ (LieModule.toEnd ℂ g (QuotientCarrier D lam)))

private theorem quotient_lie_action (lam : D.Weight) (a : g) (x : QuotientCarrier D lam) :
    (ι ℂ a) • x = ⁅a, x⁆ :=
  quotient_smul_ι D lam a x

private theorem raisingVectors :
    SimpleHighestWeightQuotient.RaisingVectors D.cartan D.direction D.e :=
  fun i => ⟨(D.triple i).e_mem, (D.triple i).e_ne_zero⟩

private theorem quotientHighestWeight (lam : D.Weight) :
    SimpleHighestWeightQuotient.IsHighestWeight D.e lam
      (quotientHighestVector D.cartan D.direction (character D lam)) :=
  (_root_.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.simple_quotient
    D.semisimple D.cartan D.direction D.regular lam (character D lam) (character_unique D lam).1
    D.e (raisingVectors D)).2

/-- Every pinned L(λ) is a simple object of O with its canonical highest-weight generator. -/
theorem simpleQuotient_in_O : SimpleQuotientInOType.{u} := by
  intro g _ _ _ D lam
  let x : QuotientCarrier D lam := quotientHighestVector D.cartan D.direction (character D lam)
  have hL := surjective_mem_O D (verma_mem_O D lam).1 (quotientMap D lam)
    (quotientMap_surjective D lam)
  let := simpleQuotient_simple D lam
  refine ⟨hL, (simple_iff_isSimpleModule D ⟨L D lam, hL⟩).mpr inferInstance, ?_⟩
  have hx := (_root_.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.highest_weight_iff_positive
    D.semisimple D.cartan D.direction D.e (raisingVectors D) _ lam x).mp
      (quotientHighestWeight D lam)
  refine ⟨hx.1, (mem_weightSpace D.cartan (L D lam) lam x).mpr (fun h => ?_), fun z => ?_,
    IsSimpleModule.span_singleton_eq_top (U g) hx.1⟩
  · change (ι ℂ (h : g)) • x = (algebraMap ℂ (U g) (lam h)) • x
    rw [algebraMap_smul, quotient_lie_action]
    exact hx.2.1 h
  · exact (quotient_lie_action D lam (z : g) x).trans (hx.2.2.1 z)

/-- Distinct highest weights give nonisomorphic simple quotients. -/
theorem simpleQuotient_equiv_iff : SimpleQuotientEquivIffType.{u} := by
  intro g _ _ _ D lam mu
  constructor
  · rintro ⟨e⟩
    let f := lieHomOfEnvelopingHom (quotient_lie_action D lam) (quotient_lie_action D mu) e.toLinearMap
    let E : QuotientCarrier D lam ≃ₗ⁅ℂ,g⁆ QuotientCarrier D mu :=
      ⟨f, e.symm, e.left_inv, e.right_inv⟩
    exact _root_.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.highest_weight_eq_of_equiv
      D.semisimple D.cartan D.direction D.regular D.e (raisingVectors D) _ _ lam mu _ _
      (quotientHighestWeight D lam) (quotientHighestWeight D mu) E
  · rintro rfl
    exact ⟨LinearEquiv.refl _ _⟩

open Specs.RepTheorySurvey.CategoryO.WeightBounds (support)
open SerreRelations (positive)
open private positiveRoot_mem_cone
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal

private theorem exists_singularVector (X : ModuleCat.{v} (U g)) (hX : objects D X)
    [Nontrivial X] :
    ∃ (lam : D.Weight) (x : X), x ≠ 0 ∧ x ∈ weightSpace D.cartan X lam ∧
      ∀ z : D.nPlus, (ι ℂ (z : g)) • x = 0 := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  have hne : (support D X).Nonempty := by
    by_contra! h
    have hbot (μ : D.Weight) : weightSpace D.cartan X μ = ⊥ :=
      not_not.mp (Set.eq_empty_iff_forall_notMem.mp h μ)
    have heq : (⨆ μ, weightSpace D.cartan X μ) = ⊤ := hX.2.1.submodule_iSup_eq_top
    exact bot_ne_top (by simpa only [hbot, iSup_bot] using heq)
  obtain ⟨ν, hν⟩ := hne
  obtain ⟨s, hs⟩ := (weightBounds D X hX).2
  let above := {μ ∈ support D X | weightLE D ν μ}
  have hfin : above.Finite := (finiteUpward D s ν).subset
    (fun μ hμ => ⟨hμ.2, hs μ hμ.1⟩)
  have hn : above.Nonempty :=
    ⟨ν, hν, _root_.LieAlgebrasAndRepresentations.HighestWeight.weightLE_refl D.alpha ν⟩
  obtain ⟨lam, hlam⟩ := hfin.exists_maximalFor D.direction above hn
  obtain ⟨x, hx, hx0⟩ := ((weightSpace D.cartan X lam).ne_bot_iff).mp hlam.prop.1
  refine ⟨lam, x, hx0, hx, ?_⟩
  let T : g →ₗ[ℂ] X := (restrictedRepresentation X (g := g)).toLinearMap.flip x
  have hker : D.nPlus.toSubmodule ≤ T.ker := by
    rw [(root_parts D).1]
    apply iSup_le
    intro α a ha
    change (ι ℂ a) • x = 0
    by_contra hax
    have ha0 : a ≠ 0 := fun h => hax (by simp [h])
    have hroot : α.val ∈ positive D.cartan D.direction :=
      ⟨⟨fun h => α.property.ne' (by simp [h]), fun h => ha0 ((Submodule.mem_bot ℂ).mp (h ▸ ha))⟩,
        α.property⟩
    have hcone := positiveRoot_mem_cone D.cartan D.direction D.semisimple ⟨α.val, hroot⟩
    have hle : weightLE D lam (lam + α.val) := by
      change (lam + α.val) - lam ∈ QPlus D
      rwa [add_sub_cancel_left]
    have hweight : (ι ℂ a) • x ∈ weightSpace D.cartan X (lam + α.val) :=
      _root_.LieAlgebrasAndRepresentations.HighestWeight.root_action X D.cartan α.val lam a x ha hx
    have hsupp : lam + α.val ∈ support D X := by
      intro h
      exact hax ((Submodule.mem_bot ℂ).mp (h ▸ hweight))
    have habove : lam + α.val ∈ above :=
      ⟨hsupp, _root_.LieAlgebrasAndRepresentations.HighestWeight.weightLE_trans D.alpha hlam.prop.2 hle⟩
    have hlt : D.direction lam < D.direction (lam + α.val) := by
      rw [map_add]
      exact lt_add_of_pos_right _ α.property
    exact hlt.not_ge (hlam.2 habove hlt.le)
  intro z
  exact hker z.property

private theorem isSimpleModule_equiv_simpleQuotient (X : ModuleCat.{v} (U g))
    (hX : objects D X) [IsSimpleModule (U g) X] :
    ∃ lam : D.Weight, Nonempty (X ≃ₗ[U g] L D lam) := by
  let := IsSimpleModule.nontrivial (U g) X
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  obtain ⟨lam, x, hx0, hx, hkill⟩ := exists_singularVector D X hX
  have he (i : D.Simple) : ⁅D.e i, x⁆ = 0 := by
    have hi : D.e i ∈ D.nPlus := by
      change D.e i ∈ D.nPlus.toSubmodule
      rw [(root_parts D).1]
      exact Submodule.mem_iSup_of_mem ⟨D.alpha i, i.property.1.2⟩ (D.triple i).e_mem
    exact hkill ⟨D.e i, hi⟩
  have hx' : ∀ h : D.cartan, ⁅(h : g), x⁆ = lam h • x :=
    (mem_weightSpace D.cartan X lam x).mp hx
  have hchar := (character_unique D lam).1
  obtain ⟨p, hp, _⟩ := (_root_.LieAlgebrasAndRepresentations.VermaWeightsUniversal.verma_universal
    D.semisimple D.cartan D.direction D.regular lam (character D lam) hchar
    D.e (raisingVectors D) X x hx' he).1
  let q : induced_value D.cartan D.direction (character D lam) →ₗ[U g] X :=
    envelopingHomOfLieHom (fun _ _ => rfl) (fun _ _ => rfl) p
  have hsurj : Function.Surjective p := by
    change Function.Surjective q
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← IsSimpleModule.span_singleton_eq_top (U g) hx0]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      ⟨highestVector_value D.cartan D.direction (character D lam), hp⟩)
  let : IsSimpleOrder (LieSubmodule ℂ g X) :=
    (submoduleOrderIso X).isSimpleOrder_iff.mp inferInstance
  obtain ⟨e, _, _⟩ :=
    _root_.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.unique_simple_quotient
      D.semisimple D.cartan D.direction D.regular lam (character D lam) hchar X p hsurj
  let F : X →ₗ[U g] QuotientCarrier D lam :=
    envelopingHomOfLieHom (fun _ _ => rfl) (quotient_lie_action D lam) e.toLieModuleHom
  exact ⟨lam, ⟨LinearEquiv.ofBijective F e.toLinearEquiv.bijective⟩⟩

/-- The simple objects of O are exactly the L(λ), with a unique label. -/
theorem simpleClassification : ClassificationType.{u, v} := by
  intro g _ _ _ D X
  rw [simple_iff_isSimpleModule D X]
  constructor
  · intro h
    let := h
    obtain ⟨lam, ⟨e⟩⟩ := isSimpleModule_equiv_simpleQuotient D X.obj X.property
    refine ⟨lam, ⟨e⟩, fun mu ⟨f⟩ => ?_⟩
    exact (simpleQuotient_equiv_iff D mu lam).mp ⟨f.symm.trans e⟩
  · rintro ⟨lam, ⟨e⟩, _⟩
    exact e.isSimpleModule_iff.mpr (simpleQuotient_simple D lam)

end SimpleQuotients

end RepTheorySurvey.CategoryO
