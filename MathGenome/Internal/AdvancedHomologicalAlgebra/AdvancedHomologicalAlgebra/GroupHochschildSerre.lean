import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCompositionCommShift
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GrothendieckEdges
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.RightDerivedComposition
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
open Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large
open AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
open AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
open AdvancedHomologicalAlgebra.GrothendieckEdges AdvancedHomologicalAlgebra.G05FilteredEdges
open AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality
open AdvancedHomologicalAlgebra

namespace AdvancedHomologicalAlgebra.GroupHochschildSerre

universe u v w

open scoped MonoidAlgebra

section HomogeneousTuplePullback


variable {k : Type u} {G H : Type v} [CommRing k] [Group G] [Group H]

/-- The map on degree (n) homogeneous bar chains applies the group map to
every vertex. -/
def homogeneousBarMapDegree (h : H →* G) (n : ℕ) :
    GroupBar.Large.B.{u,v,w} k H n ⟶
      (Rep.resFunctor (k := k) h).obj (GroupBar.Large.B.{u,v,w} k G n) :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap k k (fun c => ULift.up (h ∘ c.down)), fun g => by
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change (MonoidAlgebra.mapDomainLinearMap k k (fun t : ULift.{w} (Fin (n+1) → H) =>
        (ULift.up (h ∘ t.down) : ULift.{w} (Fin (n+1) → G))))
        ((GroupBar.Large.B.{u,v,w} k H n).ρ g (GroupBar.Large.single k H c 1)) =
      (GroupBar.Large.B.{u,v,w} k G n).ρ (h g)
        ((MonoidAlgebra.mapDomainLinearMap k k (fun t : ULift.{w} (Fin (n+1) → H) =>
          (ULift.up (h ∘ t.down) : ULift.{w} (Fin (n+1) → G))))
          (GroupBar.Large.single k H c 1))
    rw [GroupBar.Large.diagonal_action]
    simp only [GroupBar.Large.single, MonoidAlgebra.mapDomainLinearMap_single]
    rw [← GroupBar.Large.single, GroupBar.Large.diagonal_action]
    congr 1
    funext i
    exact map_mul h g (c i)⟩

@[simp]
lemma homogeneousBarMapDegree_single (h : H →* G) (n : ℕ) (c : Fin (n+1) → H) (r : k) :
    (homogeneousBarMapDegree.{u,v,w} h n).hom (GroupBar.Large.single k H c r) =
      GroupBar.Large.single k G (h ∘ c) r :=
  MonoidAlgebra.mapDomainLinearMap_single _ r _

/-- The vertexwise group map commutes with signed deletion on bar chains. -/
def homogeneousBarMap (h : H →* G) :
    GroupBar.Large.complex.{u,v,w} k H ⟶
      ((Rep.resFunctor (k := k) h).mapHomologicalComplex (.down ℕ)).obj
        (GroupBar.Large.complex.{u,v,w} k G) where
  f := homogeneousBarMapDegree h
  comm' i j hij := by
    obtain rfl : i = j + 1 := Eq.symm hij
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    change Fin (j + 2) → H at c
    apply LinearMap.ext_ring
    change GroupBar.Large.d.{u,v,w} k G j
        ((homogeneousBarMapDegree.{u,v,w} h (j+1)).hom (GroupBar.Large.single k H c 1)) =
      (homogeneousBarMapDegree.{u,v,w} h j).hom
        (GroupBar.Large.d.{u,v,w} k H j (GroupBar.Large.single k H c 1))
    rw [homogeneousBarMapDegree_single.{u,v,w}, GroupBar.Large.boundary_single.{u,v,w},
      GroupBar.Large.boundary_single.{u,v,w}, _root_.map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [homogeneousBarMapDegree_single.{u,v,w}]
    rfl

lemma homogeneousBarMap_augmentation (h : H →* G) :
    (homogeneousBarMap.{u,v,w} (k := k) h).f 0 ≫
      (Rep.resFunctor (k := k) h).map (GroupBar.Large.augmentation.{u,v,w} k G) =
    GroupBar.Large.augmentation.{u,v,w} k H := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  change Fin 1 → H at c
  apply LinearMap.ext_ring
  change ULift.up (GroupBar.Large.ε.{u,v,w} k G
    ((homogeneousBarMapDegree.{u,v,w} h 0).hom (GroupBar.Large.single k H c 1))) =
      ULift.up (GroupBar.Large.ε.{u,v,w} k H (GroupBar.Large.single k H c 1))
  rw [homogeneousBarMapDegree_single.{u,v,w}, GroupBar.Large.augmentation_single.{u,v,w},
    GroupBar.Large.augmentation_single.{u,v,w}]

/-- Pullback of homogeneous cochains for a group map and a compatible
coefficient homomorphism. -/
def homogeneousPullback (h : H →* G) {A : Rep.{max u v w} k G}
    {B : Rep.{max u v w} k H} (b : Rep.res h A ⟶ B) :
    (repHomogeneousFunctor.{u,v,w} k G).obj A ⟶ (repHomogeneousFunctor.{u,v,w} k H).obj B where
  f n := ModuleCat.ofHom
    { toFun := fun φ => (homogeneousBarMap.{u,v,w} h).f n ≫
        (Rep.resFunctor h).map φ ≫ b
      map_add' := fun x y => by
        change _ ≫ (Rep.resFunctor h).map (x+y) ≫ _ = _
        rw [(Rep.resFunctor h).map_add]
        simp only [Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun r x => by
        change _ ≫ (Rep.resFunctor h).map (r • x) ≫ _ = _
        rw [(Rep.resFunctor h).map_smul]
        simp only [Linear.smul_comp, Linear.comp_smul, RingHom.id_apply] }
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change (GroupBar.Large.complex.{u,v,w} k H).d j i ≫
        (homogeneousBarMap.{u,v,w} h).f i ≫ (Rep.resFunctor h).map φ ≫ b =
      (homogeneousBarMap.{u,v,w} h).f j ≫
        (Rep.resFunctor h).map ((GroupBar.Large.complex.{u,v,w} k G).d j i ≫ φ) ≫ b
    rw [Functor.map_comp, ← Category.assoc ((GroupBar.Large.complex.{u,v,w} k H).d j i),
      ← (homogeneousBarMap.{u,v,w} (k := k) h).comm, Category.assoc, Category.assoc]
    rfl

lemma homogeneousPullback_apply (h : H →* G) {A : Rep.{max u v w} k G}
    {B : Rep.{max u v w} k H} (b : Rep.res h A ⟶ B) (n : ℕ)
    (φ : GroupBar.Large.B.{u,v,w} k G n ⟶ A) (c : Fin (n+1) → H) :
    (((homogeneousPullback.{u,v,w} h b).f n).hom φ).hom (GroupBar.Large.single k H c 1) =
      b.hom (φ.hom (GroupBar.Large.single k G (h ∘ c) 1)) := by
  change b.hom (φ.hom ((homogeneousBarMapDegree.{u,v,w} h n).hom
    (GroupBar.Large.single k H c 1))) = _
  rw [homogeneousBarMapDegree_single]

variable (k G) (N : Subgroup G)

/-- Restriction on homogeneous cochains pulls tuples back along the subgroup
inclusion and keeps their values in the same coefficient module. -/
def restrictionCochain :
    repHomogeneousFunctor.{u,v,w} k G ⟶
      Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.restriction.{u,v,w} k G N ⋙
        repHomogeneousFunctor.{u,v,w} k N where
  app M := homogeneousPullback N.subtype (𝟙 _)
  naturality M L f := by
    ext n φ
    rfl

theorem restrictionCochain_formula : RestrictionFormula.{u,v,w} k G N (restrictionCochain k G N) := by
  intro M n φ c
  exact homogeneousPullback_apply N.subtype (𝟙 (Rep.res N.subtype M)) n φ c

variable [N.Normal]

/-- Inflation on homogeneous cochains pulls tuples back along the quotient
and includes the fixed coefficients in the original module. -/
def inflationCochain :
    subgroupInvariants.{u,v,w} k G N ⋙ repHomogeneousFunctor.{u,v,w} k (G ⧸ N) ⟶
      repHomogeneousFunctor.{u,v,w} k G where
  app M := homogeneousPullback (QuotientGroup.mk' N) (Rep.ofHom (Representation.quotientToInvariants_lift M.ρ N))
  naturality M L f := by
    ext n φ
    rfl

theorem inflationCochain_formula : InflationFormula.{u,v,w} k G N (inflationCochain k G N) := by
  intro M n φ c
  change (φ.hom ((homogeneousBarMapDegree.{u,v,w} (QuotientGroup.mk' N) n).hom
    (GroupBar.Large.single k G c 1))).val = _
  rw [homogeneousBarMapDegree_single.{u,v,w}]
  rfl

end HomogeneousTuplePullback

variable (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]

local instance standardDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

local instance repInjectives (R : Type u) (H : Type v) [CommRing R] [Group H] :
    EnoughInjectives (Rep.{max u v w} R H) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughInjectives_iff.mpr inferInstance

local instance : (subgroupInvariants.{u,v,w} k G N).IsRightAdjoint :=
  (inflationInvariantsAdjunction.{u,v,w} k G N).isRightAdjoint

/-- Normal-subgroup invariants carry G-injectives to quotient-injectives,
so the acyclicity condition in the composition theorem holds. -/
theorem composition : CompositionStatement.{u,v,w} k G N := by
  apply GrothendieckEdges.grothendieck_edges
  intro I hI
  let _ : Injective I := hI
  exact AcyclicTermComparison.rightAcyclic_of_injective _ _

/-- Taking quotient invariants of the normal-subgroup invariants gives the
original fixed submodule by forgetting the intermediate subtype. -/
def totalInvariantsIso : totalInvariants.{u,v,w} k G N ≅ Rep.invariantsFunctor.{max u v w} k G :=
  NatIso.ofComponents (fun M =>
    (show ((totalInvariants.{u,v,w} k G N).obj M) ≃ₗ[k] (Rep.invariantsFunctor k G).obj M from
      { toFun := fun x => ⟨x.val.val, fun g =>
          congrArg Subtype.val (x.property (QuotientGroup.mk' N g))⟩
        invFun := fun x => ⟨⟨x.val, fun b => x.property b⟩, fun q => by
          induction q using QuotientGroup.induction_on with
          | H g => exact Subtype.ext (x.property g)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }).toModuleIso)
    (fun _ => by ext x; rfl)


/-- The homogeneous subgroup cohomology functor equipped with its actual
quotient action. Coefficient morphisms are induced by postcomposition. -/
def subgroupCohomology (q : ℕ) : Rep.{max u v w} k G ⥤ Rep.{max u v w} k (G ⧸ N) where
  obj M := Rep.of (quotientCohomologyRepresentation.{u,v,w} k G N M q)
  map {M L} f := Rep.ofHom
    ⟨(HomologicalComplex.homologyMap (coefficientCochainMap.{u,v,w} k G N f) q).hom, fun g => by
      induction g using QuotientGroup.induction_on with
      | H g =>
        have h := congrArg (fun t => HomologicalComplex.homologyMap t q)
          (homogeneousAction_natural.{u,v,w} k G N f g)
        simp only [HomologicalComplex.homologyMap_comp] at h
        apply LinearMap.ext
        intro x
        exact congrArg (fun t => t.hom x) h⟩
  map_id M := by
    have h : coefficientCochainMap.{u,v,w} k G N (𝟙 M) = 𝟙 _ := by
      ext j φ
      change φ ≫ Rep.resMap N.subtype (𝟙 M) = φ
      exact Category.comp_id _
    ext x
    change (HomologicalComplex.homologyMap (coefficientCochainMap.{u,v,w} k G N (𝟙 M)) q).hom x = x
    rw [h, HomologicalComplex.homologyMap_id]
    rfl
  map_comp {M L V} f g := by
    have h : coefficientCochainMap.{u,v,w} k G N (f ≫ g) =
        coefficientCochainMap.{u,v,w} k G N f ≫ coefficientCochainMap.{u,v,w} k G N g := by
      ext j φ
      change φ ≫ Rep.resMap N.subtype (f ≫ g) = (φ ≫ Rep.resMap N.subtype f) ≫
        Rep.resMap N.subtype g
      exact (Category.assoc φ (Rep.resMap N.subtype f) (Rep.resMap N.subtype g)).symm
    ext x
    change (HomologicalComplex.homologyMap (coefficientCochainMap.{u,v,w} k G N (f ≫ g)) q).hom x =
      (HomologicalComplex.homologyMap (coefficientCochainMap.{u,v,w} k G N g) q).hom
        ((HomologicalComplex.homologyMap (coefficientCochainMap.{u,v,w} k G N f) q).hom x)
    rw [h, HomologicalComplex.homologyMap_comp]
    rfl

/-- The subgroup comparison keeps the underlying homogeneous cohomology
module and equips it with the descended action. -/
def subgroupUnderlyingIso (q : ℕ) :
    subgroupCohomology k G N q ⋙ forgetQuotient.{u,v,w} k G N ≅
      restriction.{u,v,w} k G N ⋙ repHomogeneousCohomology.{u,v,w} k N q :=
  NatIso.ofComponents (fun M => eqToIso ((show
    (subgroupCohomology k G N q ⋙ forgetQuotient.{u,v,w} k G N).obj M =
      (restriction.{u,v,w} k G N ⋙ repHomogeneousCohomology.{u,v,w} k N q).obj M from rfl))) (fun f => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

lemma subgroupUnderlying_conjugation (M : Rep.{max u v w} k G) :
    ∃ a : G →* End (homogeneousComplex.{u,v,w} k G N M), ActionFormula.{u,v,w} k G N M a ∧
      ∀ (q : ℕ) (g : G) (x : (homogeneousComplex.{u,v,w} k G N M).homology q),
        let t := ((subgroupUnderlyingIso k G N q).hom.app M).hom
        let y := ((subgroupUnderlyingIso k G N q).inv.app M).hom x
        t (((subgroupCohomology k G N q).obj M).ρ (QuotientGroup.mk' N g) y) =
          (HomologicalComplex.homologyMap (a g).asHom q).hom x := by
  refine ⟨homogeneousAction.{u,v,w} k G N M, homogeneousAction_formula.{u,v,w} k G N M, ?_⟩
  intro q g x
  change ((subgroupCohomology k G N q).obj M).ρ (QuotientGroup.mk' N g) x = _
  rw [show ((subgroupCohomology k G N q).obj M).ρ =
    quotientCohomologyRepresentation.{u,v,w} k G N M q from rfl]
  rfl

section CohomologicalPostcomposition
variable {A B C : Type*} [Category A] [Abelian A] [Category B] [Abelian B] [Category C] [Abelian C]

/-- Apply an exact functor to the values and boundaries of a cohomological system. -/
def postcomposeCohomological (U : B ⥤ C) [U.PreservesZeroMorphisms]
    (T : CohomologicalSystem A B) : CohomologicalSystem A C where
  value n := T.value n ⋙ U
  δ h n := U.map (T.δ h n)

private lemma mapExactPair (U : B ⥤ C) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z} (h : ExactPair f g) :
    ExactPair (U.map f) (U.map g) where
  zero := by rw [← U.map_comp, h.zero, U.map_zero]
  exact := h.exact.map U

lemma isCohomological_postcompose (U : B ⥤ C) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {T : CohomologicalSystem A B} (h : IsCohomological T) :
    IsCohomological (postcomposeCohomological U T) where
  additive n := by
    let := h.additive n
    change (T.value n ⋙ U).Additive
    infer_instance
  naturality hS hS' f n := by
    change U.map ((T.value n).map f.τ₃) ≫ U.map (T.δ hS' n) =
      U.map (T.δ hS n) ≫ U.map ((T.value (n+1)).map f.τ₁)
    rw [← U.map_comp, ← U.map_comp, h.naturality hS hS' f n]
  exact₁ hS n := mapExactPair U (h.exact₁ hS n)
  exact₂ hS n := mapExactPair U (h.exact₂ hS n)
  exact₃ hS n := mapExactPair U (h.exact₃ hS n)
  mono_zero {S} hS := by
    let := h.mono_zero hS
    change Mono (U.map ((T.value 0).map S.f))
    infer_instance

lemma postcomposeCohomological_injective_vanishing (U : B ⥤ C) [U.PreservesZeroMorphisms]
    {T : CohomologicalSystem A B} (h : ∀ (I : A) [Injective I] (n : ℕ), IsZero ((T.value (n+1)).obj I))
    (I : A) [Injective I] (n : ℕ) : IsZero (((postcomposeCohomological U T).value (n+1)).obj I) :=
  U.map_isZero (h I n)

/-- A natural transformation acts on a postcomposed cohomological system termwise. -/
def postcomposeCohomologicalMorphism {U V : B ⥤ C} [U.PreservesZeroMorphisms]
    [V.PreservesZeroMorphisms] (η : U ⟶ V) (T : CohomologicalSystem A B) :
    CohomologicalMorphism (postcomposeCohomological U T) (postcomposeCohomological V T) where
  component n := whiskerLeft (T.value n) η
  comm hS n := η.naturality (T.δ hS n)

end CohomologicalPostcomposition

section BarNormalization
variable (H : Type v) [Group H]
private abbrev Homogeneous := repHomogeneousFunctor.{u,v,w} k H
private abbrev Inv := Rep.invariantsFunctor.{max u v w} k H

private def normFromFixed (M : Rep.{max u v w} k H) (m : (Inv.{u,v,w} k H).obj M) :
    GroupBar.Large.trivial.{u,v,w} k H ⟶ M :=
  Rep.ofHom ⟨(ULift.moduleEquiv : ULift.{max v w} k ≃ₗ[k] k).toLinearMap.smulRight m.val, fun b => by
    apply LinearMap.ext
    intro r
    change r.down • m.val = M.ρ b (r.down • m.val)
    have hm := m.property b
    change M.ρ b m.val = m.val at hm
    rw [_root_.map_smul, hm]⟩

private def normFromFixedEquiv (M : Rep.{max u v w} k H) :
    (Inv.{u,v,w} k H).obj M ≃ₗ[k] (GroupBar.Large.trivial.{u,v,w} k H ⟶ M) where
  toFun := normFromFixed k H M
  invFun φ := ⟨φ.hom (ULift.up (1 : k)), fun b => (Rep.hom_comm_apply φ b (ULift.up 1)).symm⟩
  left_inv m := Subtype.ext (one_smul k m.val)
  right_inv φ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro r
    change r.down • φ.hom (ULift.up (1 : k)) = φ.hom r
    rw [← _root_.map_smul]
    congr 1
    exact ULift.ext (mul_one r.down)
  map_add' m n := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    ext r
    exact smul_add r.down m.val n.val
  map_smul' a m := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    ext r
    exact smul_comm r.down a m.val

private lemma normExact {S : ShortComplex (Rep.{max u v w} k H)} (hS : S.ShortExact) :
    (S.map (Homogeneous.{u,v,w} k H)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  letI : Projective (Opposite.unop (Opposite.op ((GroupBar.Large.complex.{u,v,w} k H).X n))) :=
    (GroupQuotientCohomologyAction.barResolution.{u,v,w} k H).projective n
  letI := hS.mono_f
  letI := hS.epi_g
  apply ModuleCat.shortComplex_shortExact
  · intro f
    change f ≫ S.g = 0 ↔ ∃ e, e ≫ S.f = f
    constructor
    · exact fun h => ⟨hS.exact.lift f h, hS.exact.lift_f f h⟩
    · rintro ⟨e, rfl⟩
      simp
  · intro f g h
    exact (cancel_mono S.f).mp h
  · intro f
    exact ⟨Projective.factorThru f S.g, Projective.factorThru_comp f S.g⟩

private abbrev NormComplex (M : Rep.{max u v w} k H) := (Homogeneous.{u,v,w} k H).obj M

private def normCycles (M : Rep.{max u v w} k H) (m : (Inv.{u,v,w} k H).obj M) :
    (NormComplex k H M).cycles 0 :=
  (NormComplex k H M).cyclesMk (GroupBar.Large.augmentation k H ≫ normFromFixed k H M m)
    1 (by simp) (by
      change (GroupBar.Large.boundary k H 0) ≫ _ = 0
      rw [← Category.assoc, GroupBar.Large.boundary_augmentation, zero_comp])

private lemma normCycles_formula (M : Rep.{max u v w} k H) (m : (Inv.{u,v,w} k H).obj M)
    (c : Fin 1 → H) :
    (((NormComplex k H M).iCycles 0).hom (normCycles k H M m)).hom
      (GroupBar.Large.single k H c 1) = m.val := by
  change (((NormComplex k H M).iCycles 0).hom
    ((NormComplex k H M).cyclesMk _ 1 _ _)).hom _ = _
  rw [show ((NormComplex k H M).iCycles 0).hom
    ((NormComplex k H M).cyclesMk _ 1 _ _) = _ from (NormComplex k H M).i_cyclesMk _ _ _ _]
  change (normFromFixed k H M m).hom
    ((GroupBar.Large.augmentation.{u,v,w} k H).hom (GroupBar.Large.single k H c 1)) = _
  rw [GroupQuotientCohomologyAction.barAugmentation_single]
  exact one_smul k m.val

private lemma normCycleImage (M : Rep.{max u v w} k H) (m : (Inv.{u,v,w} k H).obj M) :
    ((NormComplex k H M).iCycles 0).hom (normCycles k H M m) =
      GroupBar.Large.augmentation k H ≫ normFromFixed k H M m :=
  (NormComplex k H M).i_cyclesMk _ _ _ _

private def normCyclesEquiv (M : Rep.{max u v w} k H) :
    (Inv.{u,v,w} k H).obj M ≃ₗ[k] (NormComplex k H M).cycles 0 :=
  LinearEquiv.ofBijective {
    toFun := normCycles k H M
    map_add' := fun m n => by
      apply (ModuleCat.mono_iff_injective ((NormComplex k H M).iCycles 0)).mp inferInstance
      rw [_root_.map_add, normCycleImage, normCycleImage, normCycleImage]
      change _ ≫ normFromFixedEquiv k H M (m + n) = _
      rw [_root_.map_add, Preadditive.comp_add]
      rfl
    map_smul' := fun r m => by
      apply (ModuleCat.mono_iff_injective ((NormComplex k H M).iCycles 0)).mp inferInstance
      rw [_root_.map_smul, normCycleImage, normCycleImage]
      change _ ≫ normFromFixedEquiv k H M (r • m) = _
      rw [_root_.map_smul, Linear.comp_smul]
      rfl
  } (by
    constructor
    · intro m n h
      change normCycles k H M m = normCycles k H M n at h
      apply Subtype.ext
      rw [← normCycles_formula k H M m (fun _ => 1), ← normCycles_formula k H M n (fun _ => 1), h]
    · intro z
      let P := GroupQuotientCohomologyAction.barResolution.{u,v,w} k H
      let C := NormComplex k H M
      let f := (C.iCycles 0).hom z
      have hf : P.complex.d 1 0 ≫ f = 0 := by
        change (C.d 0 1).hom ((C.iCycles 0).hom z) = 0
        exact congrArg (fun t => t.hom z) (C.iCycles_d 0 1)
      let c := CokernelCofork.ofπ f hf
      let φ := P.isColimitCokernelCofork.desc c
      have hφ : GroupBar.Large.augmentation.{u,v,w} k H ≫ φ = f := by
        rw [← GroupQuotientCohomologyAction.barResolution_π_f_zero]
        exact P.isColimitCokernelCofork.fac c WalkingParallelPair.one
      let m := (normFromFixedEquiv k H M).symm φ
      refine ⟨m, (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance ?_⟩
      change (C.iCycles 0).hom (normCycles k H M m) = f
      rw [normCycleImage]
      change GroupBar.Large.augmentation k H ≫ normFromFixedEquiv k H M m = f
      rw [LinearEquiv.apply_symm_apply]
      exact hφ)

private def normDegreeZero :
    Inv.{u,v,w} k H ≅ repHomogeneousCohomology.{u,v,w} k H 0 :=
  NatIso.ofComponents
    (fun M => (normCyclesEquiv k H M).toModuleIso ≪≫ (NormComplex k H M).isoHomologyπ₀)
    (by
      intro M L f
      change _ ≫ (_ ≫ (NormComplex k H L).homologyπ 0) =
        (_ ≫ (NormComplex k H M).homologyπ 0) ≫ HomologicalComplex.homologyMap _ 0
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, ← Category.assoc]
      apply congrArg (fun h => h ≫ (NormComplex k H L).homologyπ 0)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      apply (ModuleCat.mono_iff_injective ((NormComplex k H L).iCycles 0)).mp inferInstance
      change ((NormComplex k H L).iCycles 0).hom (normCycles k H L _) =
        ((NormComplex k H L).iCycles 0).hom
          ((HomologicalComplex.cyclesMap ((Homogeneous k H).map f) 0).hom (normCycles k H M m))
      have h := congrArg (fun t => t.hom (normCycles k H M m))
        (HomologicalComplex.cyclesMap_i ((Homogeneous k H).map f) 0)
      change ((NormComplex k H L).iCycles 0).hom
          ((HomologicalComplex.cyclesMap ((Homogeneous k H).map f) 0).hom (normCycles k H M m)) =
        (((Homogeneous k H).map f).f 0).hom
          (((NormComplex k H M).iCycles 0).hom (normCycles k H M m)) at h
      rw [h]
      rw [normCycleImage, normCycleImage]
      change (GroupBar.Large.augmentation k H ≫ normFromFixed k H L (((Inv k H).map f).hom m)) =
        (GroupBar.Large.augmentation k H ≫ normFromFixed k H M m) ≫ f
      rw [Category.assoc]
      congr 1
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      ext r
      change r.down • f.hom m.val = f.hom (r.down • m.val)
      exact (_root_.map_smul _ _ _).symm)

private lemma normDegreeZero_formula (M : Rep.{max u v w} k H) (m : (Inv.{u,v,w} k H).obj M) :
    ((normDegreeZero k H).hom.app M).hom m = ((NormComplex k H M).homologyπ 0).hom (normCycles k H M m) :=
  rfl


private instance normHomogeneousAdditive : (Homogeneous.{u,v,w} k H).Additive where
  map_add := by intro M N f g; ext n φ; rfl

section GeneralNormalization

variable {A : Type*} [Category A] [Abelian A]
variable (L : A ⥤ Rep.{max u v w} k H) [L.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private lemma normExact_comp {S : ShortComplex A} (hS : S.ShortExact) :
    (S.map (L ⋙ Homogeneous.{u,v,w} k H)).ShortExact := by
  rw [S.map_comp]
  exact normExact k H (hS.map_of_exact L)

private def normSystem : CohomologicalSystem A (ModuleCat.{max u v w} k) where
  value n := L ⋙ repHomogeneousCohomology.{u,v,w} k H n
  δ hS n := (normExact_comp k H L hS).δ n (n+1) rfl

private lemma normSystem_cohomological : IsCohomological (normSystem k H L) := by
  refine ⟨fun n => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (L ⋙ repHomogeneousCohomology.{u,v,w} k H n).Additive
    infer_instance
  · intro S T hS hT f n
    exact (HomologicalComplex.HomologySequence.δ_naturality
      ((L ⋙ Homogeneous k H).mapShortComplex.map f)
      (normExact_comp k H L hS) (normExact_comp k H L hT) n (n+1) rfl).symm
  · intro S hS n
    exact ⟨(normExact_comp k H L hS).δ_comp n (n+1) rfl,
      (normExact_comp k H L hS).homology_exact₁ n (n+1) rfl⟩
  · intro S hS n
    exact ⟨_, (normExact_comp k H L hS).homology_exact₂ n⟩
  · intro S hS n
    exact ⟨(normExact_comp k H L hS).comp_δ n (n+1) rfl,
      (normExact_comp k H L hS).homology_exact₃ n (n+1) rfl⟩
  · intro S hS
    letI := hS.mono_f
    let e := Functor.isoWhiskerLeft L (normDegreeZero k H)
    have h := e.hom.naturality S.f
    have hmono : Mono ((L ⋙ Inv k H).map S.f ≫ e.hom.app S.X₂) := inferInstance
    rw [h] at hmono
    letI : Mono (e.hom.app S.X₁ ≫ ((normSystem k H L).value 0).map S.f) := hmono
    exact (mono_comp_iff_of_isIso (e.hom.app S.X₁) (((normSystem k H L).value 0).map S.f)).mp inferInstance

private lemma normalizedHomogeneousComparison [EnoughInjectives A]
    (T : CohomologicalSystem A (ModuleCat.{max u v w} k)) (hT : IsCohomological T)
    (hvanish : ∀ (I : A) [Injective I] (n : ℕ), IsZero ((T.value (n+1)).obj I))
    (hvanish' : ∀ (I : A) [Injective I] (n : ℕ),
      IsZero ((L ⋙ repHomogeneousCohomology.{u,v,w} k H (n+1)).obj I))
    {U : A ⥤ ModuleCat.{max u v w} k}
    (unit : U ≅ T.value 0) (inv : U ≅ L ⋙ Inv.{u,v,w} k H)
    (includeFixed : ∀ M : A, U.obj M → L.obj M)
    (hf : ∀ M m, ((inv.hom.app M).hom m).val = includeFixed M m) :
    ∃ e : ∀ n, T.value n ≅ L ⋙ repHomogeneousCohomology.{u,v,w} k H n,
      (e 0).hom = (unit.symm ≪≫ inv ≪≫ Functor.isoWhiskerLeft L (normDegreeZero k H)).hom ∧
      PreservesAugmentation.{u,v,w} k H L U (T.value 0) unit.hom includeFixed (e 0) ∧
      PreservesCochainConnectors.{u,v,w} k (L ⋙ Homogeneous.{u,v,w} k H) T.value T.δ e := by
  let e₀ := unit.symm ≪≫ inv ≪≫ Functor.isoWhiskerLeft L (normDegreeZero k H)
  have hC := normSystem_cohomological k H L
  have uT := UniversalDeltaFunctors.universal_of_injective_vanishing T hT hvanish
  have uC := UniversalDeltaFunctors.universal_of_injective_vanishing (normSystem k H L) hC hvanish'
  obtain ⟨e, hzero, hco⟩ := GroupLowDegreesAndCoefficients.universalComparison hT hC uT uC e₀
  refine ⟨e, hzero, ?_, ⟨normExact_comp k H L, hco⟩⟩
  intro M m
  let x := (inv.hom.app M).hom m
  refine ⟨normCycles k H (L.obj M) x, ?_, ?_⟩
  · intro c
    exact (normCycles_formula k H (L.obj M) x c).trans (hf M m)
  · have h : unit.hom ≫ (e 0).hom = inv.hom ≫ (Functor.isoWhiskerLeft L (normDegreeZero k H)).hom := by
      rw [hzero]
      simp [e₀]
    change ((unit.hom ≫ (e 0).hom).app M).hom m = _
    rw [h]
    exact normDegreeZero_formula k H (L.obj M) x

end GeneralNormalization

section FixedPointNormalization

variable {A : Type*} [Category A] [Abelian A] [EnoughInjectives A]

private lemma homogeneousCohomology_vanishes_on_injective (M : Rep.{max u v w} k H)
    [Injective M] (n : ℕ) : IsZero ((repHomogeneousCohomology.{u,v,w} k H (n+1)).obj M) := by
  let E : Rep.{max u v w} k H ≌ ModuleCat.{max u v w} (MonoidAlgebra k H) :=
    Rep.equivalenceModuleMonoidAlgebra
  let : EnoughProjectives (Rep.{max u v w} k H) :=
    E.enoughProjectives_iff.mpr ModuleCat.enoughProjectives
  let : HasExt.{max u v w} (Rep.{max u v w} k H) :=
    hasExt_of_enoughProjectives.{max u v w} _
  let R := GroupQuotientCohomologyAction.barResolution.{u,v,w} k H
  let e : (repHomogeneousCohomology.{u,v,w} k H (n+1)).obj M ≅ _ :=
    GroupCochainComparison.ResolutionBridge.homologyExtIso k R M (n+1)
  let : Subsingleton (Abelian.Ext (GroupBar.Large.trivial.{u,v,w} k H) M (n+1)) :=
    Abelian.Ext.subsingleton_of_injective _ _ n
  exact (ModuleCat.isZero_of_subsingleton _).of_iso e

private lemma normalizedFixedPointComparison
    (F : A ⥤ ModuleCat.{max u v w} k) [F.Additive] [PreservesFiniteLimits F]
    (L : A ⥤ Rep.{max u v w} k H) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]
    (inv : F ≅ L ⋙ Inv.{u,v,w} k H)
    (includeFixed : ∀ M : A, F.obj M → L.obj M)
    (hf : ∀ M m, ((inv.hom.app M).hom m).val = includeFixed M m) :
    ∃ e : ∀ n, rightValue F n ≅ L ⋙ repHomogeneousCohomology.{u,v,w} k H n,
      PreservesAugmentation.{u,v,w} k H L F (rightValue F 0)
        (AdvancedHomologicalAlgebra.GrothendieckEdges.degreeZeroUnit F) includeFixed (e 0) ∧
      PreservesCochainConnectors.{u,v,w} k (L ⋙ Homogeneous.{u,v,w} k H)
        (rightValue F) (rightBoundary F) e := by
  let T := rightSystem F
  have hT : IsCohomological T := UniversalDeltaFunctors.rightDelta _ _ F
  obtain ⟨e, _, hAug, hConn⟩ := normalizedHomogeneousComparison k H L T hT
    (fun I _ n => ClassicalDerivedValues.rightInjectiveVanishing _ _ F I n)
    (fun I _ n => by
      let : Injective (L.obj I) := Functor.PreservesInjectiveObjects.injective_obj (F := L) (show Injective I from inferInstance)
      exact homogeneousCohomology_vanishes_on_injective k H (L.obj I) n)
    (AdvancedHomologicalAlgebra.GrothendieckEdges.degreeZeroIso F) inv includeFixed hf
  exact ⟨e, hAug, hConn⟩

end FixedPointNormalization

end BarNormalization

section ConnectingMaps

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  {L L' : A ⥤ CochainComplex B ℕ} [L.PreservesZeroMorphisms] [L'.PreservesZeroMorphisms]

/-- A cochain-level natural transformation commutes with the boundaries of the
coefficient short exact sequences that both cochain functors preserve. -/
lemma cochainTransformation_connectors (η : L ⟶ L') {S : ShortComplex A}
    (h : (S.map L).ShortExact) (h' : (S.map L').ShortExact) (n : ℕ) :
    h.δ n (n+1) rfl ≫ HomologicalComplex.homologyMap (η.app S.X₁) (n+1) =
      HomologicalComplex.homologyMap (η.app S.X₃) n ≫ h'.δ n (n+1) rfl := by
  let f : S.map L ⟶ S.map L' :=
    { τ₁ := η.app S.X₁
      τ₂ := η.app S.X₂
      τ₃ := η.app S.X₃
      comm₁₂ := (η.naturality S.f).symm
      comm₂₃ := (η.naturality S.g).symm }
  exact HomologicalComplex.HomologySequence.δ_naturality f h h' n (n+1) rfl

end ConnectingMaps


/-- Simultaneous conjugation of homogeneous tuples and action on coefficients,
natural in the original G-representation. -/
def subgroupCochainAction (g : G) :
    restriction.{u,v,w} k G N ⋙ repHomogeneousFunctor.{u,v,w} k N ⟶
      restriction.{u,v,w} k G N ⋙ repHomogeneousFunctor.{u,v,w} k N where
  app M := (homogeneousAction.{u,v,w} k G N M g).asHom
  naturality M L f := by
    change coefficientCochainMap.{u,v,w} k G N f ≫ (homogeneousAction.{u,v,w} k G N L g).asHom =
      (homogeneousAction.{u,v,w} k G N M g).asHom ≫ coefficientCochainMap.{u,v,w} k G N f
    exact (homogeneousAction_natural.{u,v,w} k G N f g).symm

section SubgroupNormalization

open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors

private abbrev subgroupForget := forgetQuotient.{u,v,w} k G N
private abbrev subgroupRestrict := restriction.{u,v,w} k G N
private abbrev subgroupFixed := subgroupInvariants.{u,v,w} k G N
private abbrev subgroupSourceSystem :=
  postcomposeCohomological (subgroupForget.{u,v,w} k G N)
    (rightSystem (subgroupFixed.{u,v,w} k G N))

private def subgroupFixedIso :
    subgroupFixed.{u,v,w} k G N ⋙ subgroupForget.{u,v,w} k G N ≅
      subgroupRestrict.{u,v,w} k G N ⋙ Inv.{u,v,w} k N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

private lemma subgroupBarAction_normDegreeZero (M : Rep.{max u v w} k G)
    (g : G) (m : ((subgroupFixed.{u,v,w} k G N ⋙ subgroupForget.{u,v,w} k G N).obj M)) :
    let a := homogeneousAction.{u,v,w} k G N M g
    let q := QuotientGroup.mk' N g
    let e := (normDegreeZero.{u,v,w} k N).hom.app ((subgroupRestrict.{u,v,w} k G N).obj M)
    let j := (subgroupFixedIso.{u,v,w} k G N).hom.app M
    (HomologicalComplex.homologyMap a.asHom 0).hom (e.hom (j.hom m)) =
      e.hom (j.hom (((subgroupFixed.{u,v,w} k G N).obj M).ρ q m)) := by
  dsimp only
  let L := (subgroupRestrict.{u,v,w} k G N).obj M
  let C := NormComplex.{u,v,w} k N L
  let a := (homogeneousAction.{u,v,w} k G N M g).asHom
  let j := (subgroupFixedIso.{u,v,w} k G N).hom.app M
  let q := QuotientGroup.mk' N g
  let x := j.hom m
  let y := j.hom (((subgroupFixed.{u,v,w} k G N).obj M).ρ q m)
  change (HomologicalComplex.homologyMap a 0).hom
    (((normDegreeZero k N).hom.app L).hom x) = ((normDegreeZero k N).hom.app L).hom y
  rw [normDegreeZero_formula, normDegreeZero_formula]
  have hπ := congrArg (fun f => f.hom (normCycles k N L x)) (HomologicalComplex.homologyπ_naturality a 0)
  change (HomologicalComplex.homologyMap a 0).hom
    ((C.homologyπ 0).hom (normCycles k N L x)) =
      (C.homologyπ 0).hom ((HomologicalComplex.cyclesMap a 0).hom (normCycles k N L x)) at hπ
  rw [hπ]
  congr 1
  apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
  have hi := congrArg (fun f => f.hom (normCycles k N L x)) (HomologicalComplex.cyclesMap_i a 0)
  change (C.iCycles 0).hom ((HomologicalComplex.cyclesMap a 0).hom (normCycles k N L x)) =
    (a.f 0).hom ((C.iCycles 0).hom (normCycles k N L x)) at hi
  rw [hi]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  apply LinearMap.ext_ring
  change (((a.f 0).hom ((C.iCycles 0).hom (normCycles k N L x))).hom
    (GroupBar.Large.single.{u,v,w} k N c 1)) =
      (((C.iCycles 0).hom (normCycles k N L y)).hom (GroupBar.Large.single.{u,v,w} k N c 1))
  rw [show ((a.f 0).hom ((C.iCycles 0).hom (normCycles k N L x))).hom
    (GroupBar.Large.single.{u,v,w} k N c 1) =
    M.ρ g (((C.iCycles 0).hom (normCycles k N L x)).hom
      (GroupBar.Large.single.{u,v,w} k N (fun i => MulAut.conjNormal g⁻¹ (c i)) 1))
    from homogeneousAction_formula.{u,v,w} k G N M g 0 _ c]
  rw [normCycles_formula, normCycles_formula]
  rfl


private lemma normalizedSubgroupComparison :
    ∃ e : ∀ q, rightValue (subgroupFixed.{u,v,w} k G N) q ≅ subgroupCohomology k G N q,
      PreservesAugmentation.{u,v,w} k N (subgroupRestrict.{u,v,w} k G N)
        (subgroupFixed.{u,v,w} k G N ⋙ subgroupForget.{u,v,w} k G N)
        (rightValue (subgroupFixed.{u,v,w} k G N) 0 ⋙ subgroupForget.{u,v,w} k G N)
        (whiskerRight (degreeZeroUnit (subgroupFixed.{u,v,w} k G N)) _) (fun _ m => m.val)
        (isoWhiskerRight (e 0) _ ≪≫ subgroupUnderlyingIso k G N 0) ∧
      PreservesCochainConnectors.{u,v,w} k
        (subgroupRestrict.{u,v,w} k G N ⋙ Homogeneous.{u,v,w} k N)
        (fun q => rightValue (subgroupFixed.{u,v,w} k G N) q ⋙ subgroupForget.{u,v,w} k G N)
        (fun h n => (subgroupForget.{u,v,w} k G N).map
          (rightBoundary (subgroupFixed.{u,v,w} k G N) h n))
        (fun q => isoWhiskerRight (e q) _ ≪≫ subgroupUnderlyingIso k G N q) := by
  let F := subgroupFixed.{u,v,w} k G N
  let U := subgroupForget.{u,v,w} k G N
  let L := subgroupRestrict.{u,v,w} k G N
  let T := subgroupSourceSystem.{u,v,w} k G N
  let D := normSystem.{u,v,w} k N L
  let unit := isoWhiskerRight (degreeZeroIso F) U
  let inv := subgroupFixedIso.{u,v,w} k G N
  have hT : IsCohomological T :=
    isCohomological_postcompose U (UniversalDeltaFunctors.rightDelta _ _ F)
  have hv (I : Rep.{max u v w} k G) [Injective I] (n : ℕ) : IsZero ((T.value (n+1)).obj I) :=
    U.map_isZero (ClassicalDerivedValues.rightInjectiveVanishing _ _ F I n)
  have hw (I : Rep.{max u v w} k G) [Injective I] (n : ℕ) : IsZero ((D.value (n+1)).obj I) := by
    have : Injective (L.obj I) := restriction_preservesInjectives.{u,v,w} k G N |>.injective_obj
      (show Injective I from inferInstance)
    exact homogeneousCohomology_vanishes_on_injective k N (L.obj I) n
  obtain ⟨e, hz, ha, hδ⟩ := normalizedHomogeneousComparison k N L T hT @hv @hw unit inv
    (fun _ m => m.val) (by intro _ _; rfl)
  have hD : IsCohomological D := normSystem_cohomological k N L
  have hUT := UniversalDeltaFunctors.universal_of_injective_vanishing T hT @hv
  have hc : ∀ {S : ShortComplex (Rep.{max u v w} k G)} (hS : S.ShortExact) (n : ℕ),
      T.δ hS n ≫ (e (n+1)).hom.app S.X₁ = (e n).hom.app S.X₃ ≫ D.δ hS n := by
    obtain ⟨_, h⟩ := hδ
    exact h
  let j : CohomologicalMorphism T D := ⟨fun n => (e n).hom, hc⟩
  have heq (g : G) (n : ℕ) (M : Rep.{max u v w} k G)
      (x : (T.value n).obj M) :
      (HomologicalComplex.homologyMap (homogeneousAction.{u,v,w} k G N M g).asHom n).hom
          (((e n).hom.app M).hom x) =
        ((e n).hom.app M).hom
          (((rightValue F n).obj M).ρ (QuotientGroup.mk' N g) x) := by
    let q := QuotientGroup.mk' N g
    let aQ := postcomposeCohomologicalMorphism (quotientForgetAction.{u,v,w} k G N q)
      (rightSystem F)
    let aB : CohomologicalMorphism D D :=
      { component n := whiskerRight (subgroupCochainAction.{u,v,w} k G N g)
          (HomologicalComplex.homologyFunctor _ (.up ℕ) n)
        comm hS n := cochainTransformation_connectors (subgroupCochainAction.{u,v,w} k G N g)
          (normExact_comp k N L hS) (normExact_comp k N L hS) n }
    let l := GroupLowDegreesAndCoefficients.deltaComposition aQ j
    let r := GroupLowDegreesAndCoefficients.deltaComposition j aB
    have he : l.component 0 = r.component 0 := by
      apply NatTrans.ext
      funext W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      let s := unit.inv.app W
      let s' := (degreeZeroIso F).inv.app W
      have hs := Rep.hom_comm_apply s' q y
      change ((e 0).hom.app W).hom ((((rightValue F 0).obj W).ρ q) y) =
        (HomologicalComplex.homologyMap (homogeneousAction.{u,v,w} k G N W g).asHom 0).hom
          (((e 0).hom.app W).hom y)
      rw [hz]
      change ((normDegreeZero k N).hom.app (L.obj W)).hom
          ((inv.hom.app W).hom (s.hom ((((rightValue F 0).obj W).ρ q) y))) =
        (HomologicalComplex.homologyMap (homogeneousAction.{u,v,w} k G N W g).asHom 0).hom
          (((normDegreeZero k N).hom.app (L.obj W)).hom ((inv.hom.app W).hom (s.hom y)))
      change s.hom ((((rightValue F 0).obj W).ρ q) y) = ((F.obj W).ρ q) (s.hom y) at hs
      rw [hs]
      exact (subgroupBarAction_normDegreeZero k G N W g (s.hom y)).symm
    obtain ⟨w, _, hu⟩ := hUT D hD (r.component 0)
    have hlr : l = r := (hu l he).trans (hu r rfl).symm
    exact (congrArg (fun f : CohomologicalMorphism T D => ((f.component n).app M).hom x) hlr).symm
  let f (n : ℕ) : rightValue F n ≅ subgroupCohomology k G N n :=
    NatIso.ofComponents (fun M => Rep.mkIso
      (.mk ((e n).app M).toLinearEquiv (fun q => by
        induction q using QuotientGroup.induction_on with
        | H g =>
          apply LinearMap.ext
          intro x
          exact (heq g n M x).symm))) (fun a => by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact congrArg (fun z => z.hom x) ((e n).hom.naturality a))
  have hf (n : ℕ) : isoWhiskerRight (f n) U ≪≫ subgroupUnderlyingIso k G N n = e n := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  refine ⟨f, ?_, ?_⟩
  · change PreservesAugmentation.{u,v,w} k N L (F ⋙ U) (T.value 0) unit.hom _ _
    rw [hf]
    exact ha
  · exact (funext hf) ▸ hδ

end SubgroupNormalization


private lemma normalizedQuotientComparison :
    ∃ e : ∀ n, rightValue (quotientInvariants.{u,v,w} k G N) n ≅
        repHomogeneousCohomology.{u,v,w} k (G ⧸ N) n,
      PreservesAugmentation.{u,v,w} k (G ⧸ N) (𝟭 _) (quotientInvariants.{u,v,w} k G N)
        (rightValue (quotientInvariants.{u,v,w} k G N) 0)
        (degreeZeroUnit (quotientInvariants.{u,v,w} k G N)) (fun _ m => m.val) (e 0) ∧
      PreservesCochainConnectors.{u,v,w} k (repHomogeneousFunctor.{u,v,w} k (G ⧸ N))
        (rightValue (quotientInvariants.{u,v,w} k G N))
        (rightBoundary (quotientInvariants.{u,v,w} k G N)) e :=
  normalizedFixedPointComparison k (G ⧸ N) (quotientInvariants.{u,v,w} k G N)
    (𝟭 _) (Iso.refl _) (fun _ m => m.val) (fun _ _ => rfl)

private lemma normalizedTotalComparison :
    ∃ e : ∀ n, rightValue (totalInvariants.{u,v,w} k G N) n ≅ repHomogeneousCohomology.{u,v,w} k G n,
      PreservesAugmentation.{u,v,w} k G (𝟭 _) (totalInvariants.{u,v,w} k G N)
        (rightValue (totalInvariants.{u,v,w} k G N) 0)
        (degreeZeroUnit (totalInvariants.{u,v,w} k G N)) (fun _ m => m.val.val) (e 0) ∧
      PreservesCochainConnectors.{u,v,w} k (repHomogeneousFunctor.{u,v,w} k G)
        (rightValue (totalInvariants.{u,v,w} k G N)) (rightBoundary (totalInvariants.{u,v,w} k G N)) e :=
  normalizedFixedPointComparison k G (totalInvariants.{u,v,w} k G N) (𝟭 _)
    (totalInvariantsIso k G N) (fun _ m => m.val.val) (fun _ _ => rfl)

/-- The ordinary cohomology models with their augmentation and connecting-map
comparisons. The subgroup model retains the original homogeneous carrier. -/
theorem models : Nonempty (CohomologyModels.{u,v,w} k G N) := by
  obtain ⟨s, hs₀, hsδ⟩ := normalizedSubgroupComparison.{u,v,w} k G N
  obtain ⟨q, hq₀, hqδ⟩ := normalizedQuotientComparison.{u,v,w} k G N
  obtain ⟨t, ht₀, htδ⟩ := normalizedTotalComparison.{u,v,w} k G N
  exact ⟨{
    subgroup := subgroupCohomology k G N
    subgroupDerived := s
    underlying := subgroupUnderlyingIso k G N
    subgroup_carrier := fun _ _ => rfl
    underlying_eq := fun _ _ => rfl
    conjugation := subgroupUnderlying_conjugation k G N
    quotientDerived := q
    totalDerived := t
    subgroup_augmentation := hs₀
    subgroup_connectors := hsδ
    quotient_augmentation := hq₀
    quotient_connectors := hqδ
    total_augmentation := ht₀
    total_connectors := htδ }⟩

section CanonicalCoordinates
variable {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C] [EnoughInjectives B]
  (V : B ⥤ C) [V.Additive] [PreservesFiniteLimits V]

/-- The comparison isomorphisms in the truncation span are determined by
their prescribed maps in cohomology. -/
private theorem columnTruncation_eq (n : ℤ) (T S : ColumnTruncation V n) : T = S := by
  have hL : T.lower = S.lower := Iso.ext (T.lower_hom.trans S.lower_hom.symm)
  have hP : T.point = S.point := by
    apply Iso.ext
    apply NatTrans.ext
    funext Y
    let H := DerivedCategory.Plus.homologyFunctor B n
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    let P := (T.point.app Y)
    let Q := (S.point.app Y)
    let π := (t.truncGEπ n).app ((t.truncLE n).obj Y)
    let ε := (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).app (H.obj Y)
    let S₀ := DerivedCategory.Plus.singleFunctor B n
    let X := H.obj Y
    have h : H.map π ≫ H.map P.hom ≫ ε.hom = H.map π ≫ H.map Q.hom ≫ ε.hom := by
      rw [← H.map_comp_assoc, ← H.map_comp_assoc]
      exact (T.point_normalization Y).trans (S.point_normalization Y).symm
    let := homology_truncGEπ_isIso ((t.truncLE n).obj Y) n n (by omega)
    have hm := (cancel_epi (H.map π)).mp h
    have hp := (cancel_mono ε.hom).mp hm
    let S' := DerivedCategory.singleFunctor B n
    let f : X ⟶ X := S'.preimage (DerivedCategory.Plus.ι.map (P.inv ≫ Q.hom))
    have hf : S₀.map f = P.inv ≫ Q.hom := by
      apply DerivedCategory.Plus.ι.map_injective
      exact Functor.map_preimage S' _
    have hH : H.map (S₀.map f) = 𝟙 _ := by
      rw [hf, H.map_comp, ← hp, ← H.map_comp, P.inv_hom_id]
      exact H.map_id _
    have hn' := (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.naturality f
    change H.map (S₀.map f) ≫ ε.hom = ε.hom ≫ f at hn'
    rw [hH, Category.id_comp] at hn'
    have hfid : f = 𝟙 _ := (cancel_epi ε.hom).mp (hn'.symm.trans (Category.comp_id ε.hom).symm)
    have hpq : P.inv ≫ Q.hom = 𝟙 _ := by
      rw [← hf, hfid, S₀.map_id]
      rfl
    change P.hom = Q.hom
    apply (cancel_epi P.inv).mp
    rw [P.inv_hom_id, hpq]
  cases T
  cases S
  cases hL
  cases hP
  rfl

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

/-- Any object-case package identifies its column edge with the same
canonical derived map. -/
lemma classicalColumn_eq_derivedSecondEdge
    {P : AdvancedHomologicalAlgebra.GrothendieckSpectralSequence.Package F V}
    (E : ObjectEdges F V P) (n : ℕ) :
    classicalColumn F V (E.truncation n) E.degreeZero = derivedSecondEdge V F n := by
  have h := columnTruncation_eq V (n : ℤ) (E.truncation n) (columnTruncation V (n : ℤ))
  have he : E.degreeZero.symm = (canonicalRightZeroIso V).symm := Iso.ext E.degreeZero_hom
  have he' : E.degreeZero = canonicalRightZeroIso V := congrArg Iso.symm he
  rw [h, he']
  rfl

end CanonicalCoordinates

section SequenceAssembly
variable {k G N} (C : CohomologyModels.{u,v,w} k G N) {P : Package (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N)} (E : ObjectEdges (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) P)

private lemma displayedSecond_row (n : ℕ) :
    displayedSecond C E n 0 = rowIndexIso _ _ P n ≪≫ Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre.rowCoordinates C E n ≪≫
      isoWhiskerRight (E.degreeZeroF ≪≫ C.subgroupDerived 0)
        (repHomogeneousCohomology.{u,v,w} k (G ⧸ N) n) := by
  simp only [displayedSecond, E.row_identification, Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre.rowCoordinates, isoWhiskerRight_trans,
    Iso.trans_assoc]
  rw [isoWhiskerLeft_trans_isoWhiskerRight_assoc, isoWhiskerLeft_trans_isoWhiskerRight]

private lemma displayedSecond_column (n : ℕ) :
    displayedSecond C E 0 n = columnIndexIso _ _ P n ≪≫ columnCoordinates C E n ≪≫
      isoWhiskerLeft (C.subgroup n) (E.degreeZero.symm ≪≫ C.quotientDerived 0) := by
  simp only [displayedSecond, E.column_identification, columnCoordinates, isoWhiskerLeft_trans,
    Iso.trans_assoc]
  rw [isoWhiskerLeft_trans_isoWhiskerRight_assoc]

/-- Read the ordinary edges in the displayed page and abutment coordinates. -/
def identifyFilteredGroupEdges
    (restriction : RestrictionEdge C)
    (inflationCochain : (subgroupInvariants.{u,v,w} k G N) ⋙ repHomogeneousFunctor.{u,v,w} k (G ⧸ N) ⟶
      repHomogeneousFunctor.{u,v,w} k G)
    (inflationFormula : InflationFormula k G N inflationCochain)
    (hInf : ∀ n,
      (isoWhiskerLeft (subgroupInvariants.{u,v,w} k G N) (C.quotientDerived n)).hom ≫
        whiskerRight inflationCochain (HomologicalComplex.homologyFunctor _ (.up ℕ) n) =
      derivedFirstEdge (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) P n ≫ (C.totalDerived n).hom)
    (hRes : ∀ n,
      (C.totalDerived n).hom ≫ restriction.map n =
        classicalColumn (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) (E.truncation n) E.degreeZero ≫
          (isoWhiskerRight (C.subgroupDerived n) (quotientInvariants.{u,v,w} k G N)).hom) :
    EdgeIdentifications C P E where
  restriction := restriction
  inflationCochain := inflationCochain
  inflationFormula := inflationFormula
  inflation_eq := hInf
  restriction_eq := hRes
  row_identification := displayedSecond_row C E
  column_identification := displayedSecond_column C E
  inflation_filtered n M := by
    simp only [Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre.rowCoordinates, displayedTarget, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    change (E.rowPage n).hom.app M ≫
        ((isoWhiskerLeft (subgroupInvariants.{u,v,w} k G N) (C.quotientDerived n)).hom ≫
          whiskerRight inflationCochain (HomologicalComplex.homologyFunctor _ (.up ℕ) n)).app M =
      (E.filtered M).row n ≫ (E.objectCase.targetIso n).hom.app M ≫ (C.totalDerived n).hom.app M
    rw [hInf n]
    simp only [NatTrans.comp_app]
    rw [reassoc_of% (E.first_comparison n M)]
  restriction_filtered n M := by
    simp only [columnCoordinates, displayedTarget, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    change (E.objectCase.targetIso n).hom.app M ≫ ((C.totalDerived n).hom ≫ restriction.map n).app M =
      (E.filtered M).column n ≫ (E.columnPage n).hom.app M ≫
        (isoWhiskerRight (C.subgroupDerived n) (quotientInvariants.{u,v,w} k G N)).hom.app M
    rw [hRes n]
    simp only [NatTrans.comp_app]
    rw [reassoc_of% (E.second_comparison n M)]

/-- The first-quadrant vanishing propagates from E₂ by taking homology. -/
theorem page_quadrant (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]
    {P : Package (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N)}
    (E : ObjectEdges _ _ P) (M : Rep.{max u v w} k G) (r : ℕ) (p n : ℤ)
    (hn : p < 0 ∨ n < p) : IsZero (((objectSequence _ _ P).obj M).page r p n) := by
  let D := (objectSequence _ _ P).obj M
  induction r with
  | zero => exact E.objectCase.quadrant M p n hn
  | succ r ih =>
    let p' := p - ((r : ℤ) + 2)
    let n' := n - 1
    have hp' : p' + ((r : ℤ) + 2) = p := by dsimp [p']; omega
    have hn' : n' + 1 = n := by dsimp [n']; omega
    let S := D.pageComplex r p' n'
    have hS : IsZero S.X₂ := by
      change IsZero (D.page r (p' + ((r : ℤ) + 2)) (n' + 1))
      rwa [hp', hn']
    exact (S.isZero_homology_of_isZero_X₂ hS).of_iso
      (eqToIso (by rw [hp', hn']) ≪≫ D.nextIso r p' n')

private theorem conjugateFiveTerms {D : Type*} [Category D] [Abelian D]
    {X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ Y₃ Y₄ Y₅ : D}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (e₄ : X₄ ≅ Y₄) (e₅ : X₅ ≅ Y₅)
    {f : Y₁ ⟶ Y₂} {g : Y₂ ⟶ Y₃} {d : Y₃ ⟶ Y₄} {h : Y₄ ⟶ Y₅}
    (H : ClassicalFiveTerms f g d h) :
    ClassicalFiveTerms (e₁.hom ≫ f ≫ e₂.inv) (e₂.hom ≫ g ≫ e₃.inv)
      (e₃.hom ≫ d ≫ e₄.inv) (e₄.hom ≫ h ≫ e₅.inv) := by
  let _ := H.mono
  have hfg : (e₁.hom ≫ f ≫ e₂.inv) ≫ (e₂.hom ≫ g ≫ e₃.inv) = 0 := by
    simp [reassoc_of% H.fg]
  have hgd : (e₂.hom ≫ g ≫ e₃.inv) ≫ (e₃.hom ≫ d ≫ e₄.inv) = 0 := by
    simp [reassoc_of% H.gd]
  have hdh : (e₃.hom ≫ d ≫ e₄.inv) ≫ (e₄.hom ≫ h ≫ e₅.inv) = 0 := by
    simp [reassoc_of% H.dh]
  exact ⟨inferInstance, hfg, hgd, hdh,
    exact_conjugate e₁ e₂ e₃ _ _ _ H.exact_f_g _,
    exact_conjugate e₂ e₃ e₄ _ _ _ H.exact_g_d _,
    exact_conjugate e₃ e₄ e₅ _ _ _ H.exact_d_h _⟩

/-- Transport the first-quadrant assertion and exact sequence along the same comparison maps. -/
theorem assemble (e : EdgeIdentifications C P E) :
    Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre.FullStatement.{u,v,w} k G N := by
  refine ⟨P, E, C, e, page_quadrant k G N E, ?_⟩
  intro M
  let L (n : ℕ) := isoWhiskerLeft (subgroupInvariants.{u,v,w} k G N) (C.quotientDerived n)
  let T (n : ℕ) := C.totalDerived n
  let U := isoWhiskerRight (C.subgroupDerived 1) (quotientInvariants.{u,v,w} k G N)
  have hi (n : ℕ) :
      (L n).inv.app M ≫ (derivedFirstEdge _ _ P n).app M ≫ (T n).hom.app M =
        HomologicalComplex.homologyMap (e.inflationCochain.app M) n := by
    have h := congrArg (fun t => NatTrans.app t M) (e.inflation_eq n)
    simp only [NatTrans.comp_app] at h
    rw [← h]
    exact Iso.inv_hom_id_app_assoc _ _ _
  have hr :
      (T 1).inv.app M ≫ (classicalColumn _ _ (E.truncation 1) E.degreeZero).app M ≫
        U.hom.app M = (e.restriction.map 1).app M := by
    have h := congrArg (fun t => NatTrans.app t M) (e.restriction_eq 1)
    simp only [NatTrans.comp_app] at h
    rw [← h]
    exact Iso.inv_hom_id_app_assoc _ _ _
  have H := conjugateFiveTerms ((L 1).app M).symm ((T 1).app M).symm (U.app M).symm
    ((L 2).app M).symm ((T 2).app M).symm (E.fiveTerms M)
  change ClassicalFiveTerms
    ((L 1).inv.app M ≫ (derivedFirstEdge _ _ P 1).app M ≫ (T 1).hom.app M)
    ((T 1).inv.app M ≫ (classicalColumn _ _ (E.truncation 1) E.degreeZero).app M ≫
      U.hom.app M) _ ((L 2).inv.app M ≫ (derivedFirstEdge _ _ P 2).app M ≫ (T 2).hom.app M) at H
  rw [hi 1, hr, hi 2] at H
  simpa only [ordinaryTransgression, Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre.rowCoordinates, columnCoordinates, Iso.trans_hom,
    Iso.trans_inv, NatTrans.comp_app, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc] using H


end SequenceAssembly

section Reflection
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
  {L : A ⥤ B} [L.CommShift ℤ] [L.EssSurj]
  {F G : B ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
  [(whiskerLeft L τ).CommShift ℤ]

include L in
lemma commShift_of_essSurj_precomposition : τ.CommShift ℤ where
  shift_comm a := by
    apply NatTrans.ext
    funext X
    let Y := L.objPreimage X
    let e := L.objObjPreimageIso X
    let lhs := (F.commShiftIso a).hom ≫ whiskerRight τ (shiftFunctor C a)
    let rhs := whiskerLeft (shiftFunctor B a) τ ≫ (G.commShiftIso a).hom
    change lhs.app X = rhs.app X
    have he : lhs.app (L.obj Y) = rhs.app (L.obj Y) := by
      have h := NatTrans.shift_app_comm (whiskerLeft L τ) a Y
      simp only [Functor.commShiftIso_comp_hom_app, whiskerLeft_app, Category.assoc] at h
      rw [← reassoc_of% (τ.naturality ((L.commShiftIso a).hom.app Y))] at h
      exact (cancel_epi (F.map ((L.commShiftIso a).hom.app Y))).mp h
    apply (cancel_epi ((shiftFunctor B a ⋙ F).map e.hom)).mp
    rw [lhs.naturality, rhs.naturality, he]
end Reflection

section HomotopyComposition

variable {A B C : Type*} [Category A] [Abelian A] [Category B] [Abelian B] [Category C] [Abelian C]
  (F : A ⥤ B) (U : B ⥤ C) [F.Additive] [U.Additive]

local notation "qA" => HomotopyCategory.quotient A (ComplexShape.up ℤ)
local notation "qC" => HomotopyCategory.quotient C (ComplexShape.up ℤ)

private lemma homotopyCompIso_commShift :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ U)) (.up ℤ)).hom.CommShift ℤ := by
  let fc := F.mapHomologicalComplex (.up ℤ)
  let uc := U.mapHomologicalComplex (.up ℤ)
  let fh := F.mapHomotopyCategory (.up ℤ)
  let uh := U.mapHomotopyCategory (.up ℤ)
  let t := Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ U)) (.up ℤ)
  let t₀ := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ U)) (.up ℤ)
  have ht : whiskerLeft qA t.hom =
      (Functor.associator _ _ _).inv ≫
        whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom uh ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft fc (U.mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight t₀.hom qC ≫ ((F ⋙ U).mapHomotopyCategoryFactors (.up ℤ)).inv := by
    apply NatTrans.ext
    funext K
    have hm : ((F ⋙ U).mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
    simp only [t, t₀, Functor.mapHomotopyCategoryCompIso, Quotient.natIsoLift_hom,
      whiskerLeft_app, isoWhiskerRight_hom, whiskerRight_app,
      NatTrans.comp_app, associator_hom_app, associator_inv_app, Category.id_comp,
      Functor.mapHomotopyCategoryFactors_hom_app, CategoryTheory.Functor.map_id]
    change (qC).map (t₀.hom.app K) = _
    erw [hm, Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]
  let : (whiskerLeft qA t.hom).CommShift ℤ := by
    rw [ht]
    infer_instance
  exact commShift_of_essSurj_precomposition t.hom (L := qA)


private lemma plusHomotopyCompIso_commShift :
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ U))).hom.CommShift ℤ := by
  let iA := HomotopyCategory.Plus.ι A
  let iC := HomotopyCategory.Plus.ι C
  let Fp := F.mapHomotopyCategoryPlus
  let Uh := U.mapHomotopyCategory (.up ℤ)
  let t := Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ U))
  let th := Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ U)) (.up ℤ)
  let : th.hom.CommShift ℤ := homotopyCompIso_commShift F U
  have ht : whiskerRight t.hom iC =
      (Functor.associator _ _ _).hom ≫
        whiskerLeft Fp U.mapHomotopyCategoryPlusCompι.hom ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight F.mapHomotopyCategoryPlusCompι.hom Uh ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft iA th.hom ≫
        (F ⋙ U).mapHomotopyCategoryPlusCompι.inv := by
    apply NatTrans.ext
    funext K
    simp only [t, Functor.mapHomotopyCategoryPlusCompIso, whiskerRight_app,
      Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.whiskeringRight_preimage_app,
      whiskerLeft_app, isoWhiskerLeft_hom,
      NatTrans.comp_app, associator_hom_app, associator_inv_app,
      Functor.mapHomotopyCategoryPlusCompι_hom_app, Functor.mapHomotopyCategoryPlusCompι_inv_app,
      Category.id_comp]
    change th.hom.app (iA.obj K) = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.id_comp,
      Category.comp_id]
  have hwt : NatTrans.CommShift (whiskerRight t.hom iC) ℤ := by
    rw [ht]
    infer_instance
  exact NatTrans.CommShift.of_comp_faithful iC hwt

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]

/-- The actual comparison of composed right-derived functors commutes with shift. -/
instance comparisonValue_commShift : (comparisonValue F U).CommShift ℤ := by
  let := plusHomotopyCompIso_commShift F U
  change (Functor.natTransOfIsRightDerivedFunctorComp
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ U))) DerivedCategory.Plus.Qh
    DerivedCategory.Plus.Qh DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)
    F.rightDerivedFunctorPlusUnith U.rightDerivedFunctorPlusUnith
    (F ⋙ U).rightDerivedFunctorPlusUnith).CommShift ℤ
  infer_instance

end HomotopyComposition


section CompositionAtDegreeZero
variable {A B C : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [Category C] [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (V : B ⥤ C) [F.Additive] [V.Additive]
private lemma quotientCompQhIso_hom_id {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory D] (K : CochainComplex.Plus D) :
    (DerivedCategory.Plus.quotientCompQhIso D).hom.app K = 𝟙 _ := by
  rfl

private lemma quotientCompQhIso_inv_id {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory D] (K : CochainComplex.Plus D) :
    (DerivedCategory.Plus.quotientCompQhIso D).inv.app K = 𝟙 _ := by
  rfl

omit [EnoughInjectives B] in
private lemma units_agree (K : CochainComplex.Plus A) :
    F.rightDerivedFunctorPlusUnit.app K =
      F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj K) := by
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  simp only [quotientCompQhIso_hom_id, quotientCompQhIso_inv_id,
    Functor.quotientCompMapHomotopyCategoryPlusIso, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

omit [EnoughInjectives A] [EnoughInjectives B] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] in
private lemma mapCompIso_inv_id (K : CochainComplex.Plus A) :
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ V))).inv.app
      ((HomotopyCategory.Plus.quotient A).obj K) = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  change (HomotopyCategory.quotient C (.up ℤ)).map _ = 𝟙 _
  rw [← CategoryTheory.Functor.map_id]
  congr 1

@[reassoc]
private lemma compositionUnit_app (K : CochainComplex.Plus A) :
    (F ⋙ V).rightDerivedFunctorPlusUnit.app K ≫ (comparisonValue F V).app
        (DerivedCategory.Plus.Q.obj K) =
      V.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        V.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  have h := congrArg (fun t => t.app ((HomotopyCategory.Plus.quotient A).obj K))
    ((F ⋙ V).rightDerivedFunctorPlus.rightDerived_fac
      (F ⋙ V).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A)
      (F.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus) (inputComparisonValue F V))
  simp only [inputComparisonValue, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id] at h
  rw [mapCompIso_inv_id F V K, CategoryTheory.Functor.map_id] at h
  rw [units_agree (F ⋙ V) K, units_agree V (F.mapCochainComplexPlus.obj K), units_agree F K]
  exact h.trans (Category.id_comp _)

variable (U : B ⥤ C) [U.Additive]

lemma comparisonValue_natural_right (η : V ⟶ U) :
    comparisonValue F V ≫ whiskerLeft F.rightDerivedFunctorPlus η.rightDerivedFunctorPlus =
      (whiskerLeft F η).rightDerivedFunctorPlus ≫ comparisonValue F U := by
  apply CategoryTheory.Functor.rightDerived_ext _ (F ⋙ V).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A) _
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app]
  rw [compositionUnit_app_assoc]
  have h := η.rightDerivedFunctorPlus.naturality (F.rightDerivedFunctorPlusUnit.app K)
  change V.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      η.rightDerivedFunctorPlus.app (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
    η.rightDerivedFunctorPlus.app (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) ≫
      U.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) at h
  rw [h, η.rightDerivedFunctorPlus_fac_app_assoc]
  rw [NatTrans.rightDerivedFunctorPlus_fac_app_assoc, compositionUnit_app]
  congr 2
omit [EnoughInjectives A] [EnoughInjectives B] [HasDerivedCategory A] in
private lemma mappedStalkIso_hom_app {X : A} :
    (mappedStalkIso F).hom.app X = DerivedCategory.Plus.Q.map
      (show (stalkComplex B).obj (F.obj X) ⟶ F.mapCochainComplexPlus.obj ((stalkComplex A).obj X) from
        (CochainComplex.plus B).homMk ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app X)) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [mappedStalkIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.whiskeringRight_preimage_app, Functor.FullyFaithful.map_preimage, id,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    associator_inv_app, associator_hom_app, isoWhiskerRight_hom, whiskerRight_app,
    Iso.symm_hom, Category.id_comp, Category.comp_id, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp]
  rfl

private lemma mappedStalkIso_comp_app (X : A) :
    (mappedStalkIso (F ⋙ V)).hom.app X =
      (mappedStalkIso V).hom.app (F.obj X) ≫
        DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map
          (show (stalkComplex B).obj (F.obj X) ⟶ F.mapCochainComplexPlus.obj ((stalkComplex A).obj X) from
            (CochainComplex.plus B).homMk
              ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app X))) := by
  rw [mappedStalkIso_hom_app (F ⋙ V), mappedStalkIso_hom_app V]
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply (CochainComplex.Plus.ι C).map_injective
  exact HomologicalComplex.singleMapHomologicalComplex_comp_inv_app F V (.up ℤ) 0 X

lemma stalkToDerived_comp_app (X : A) :
    (stalkToDerived (F ⋙ V)).app X ≫ (comparisonValue F V).app ((DerivedCategory.Plus.singleFunctor A 0).obj X) =
      (stalkToDerived V).app (F.obj X) ≫
        V.rightDerivedFunctorPlus.map ((stalkToDerived F).app X) := by
  let K := (stalkComplex A).obj X
  let L := (stalkComplex B).obj (F.obj X)
  let a : L ⟶ F.mapCochainComplexPlus.obj K :=
    (CochainComplex.plus B).homMk ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app X)
  simp only [stalkToDerived, NatTrans.comp_app, whiskerLeft_app, Category.assoc]
  change (mappedStalkIso (F ⋙ V)).hom.app X ≫
      (F ⋙ V).rightDerivedFunctorPlusUnit.app K ≫
      (comparisonValue F V).app (DerivedCategory.Plus.Q.obj K) =
    (mappedStalkIso V).hom.app (F.obj X) ≫ V.rightDerivedFunctorPlusUnit.app L ≫
      V.rightDerivedFunctorPlus.map ((mappedStalkIso F).hom.app X ≫ F.rightDerivedFunctorPlusUnit.app K)
  rw [compositionUnit_app, mappedStalkIso_comp_app, mappedStalkIso_hom_app F,
    CategoryTheory.Functor.map_comp, Category.assoc]
  change _ ≫ DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map a) ≫
      V.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
      V.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) = _
  have ha := V.rightDerivedFunctorPlusUnit.naturality a
  change DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map a) ≫
      V.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) =
    V.rightDerivedFunctorPlusUnit.app L ≫ V.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map a) at ha
  rw [reassoc_of% ha]

lemma derivedSecondEdge_degreeZeroUnit [PreservesFiniteLimits V] (X : A) :
    (degreeZeroUnit (F ⋙ V)).app X ≫ (derivedSecondEdge V F 0).app X =
      V.map ((degreeZeroUnit F).app X) := by
  let HB := DerivedCategory.Plus.homologyFunctor B 0
  let HC := DerivedCategory.Plus.homologyFunctor C 0
  let U := F.obj X
  let Y := (DerivedCategory.Plus.singleFunctor B 0).obj U
  let Y' := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let t := (stalkToDerived F).app X
  let c := (comparisonValue F V).app ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let εB := (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app U
  let εC := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app (V.obj U)
  change (εC ≫ HC.map ((stalkToDerived (F ⋙ V)).app X)) ≫
      (HC.map c ≫ (derivedTruncationEdge V 0).app Y') =
    V.map (εB ≫ HB.map t)
  rw [Category.assoc, ← HC.map_comp_assoc, stalkToDerived_comp_app,
    HC.map_comp_assoc]
  have ht := (derivedTruncationEdge V 0).naturality t
  change HC.map (V.rightDerivedFunctorPlus.map t) ≫ (derivedTruncationEdge V 0).app Y' =
    (derivedTruncationEdge V 0).app Y ≫ V.map (HB.map t) at ht
  rw [ht, derivedTruncationEdge_app_stalk]
  have hd : (rightDerivedStalkHomologyIso V 0).hom.app U = (canonicalRightZeroIso V).hom.app U := by
    simp [rightDerivedStalkHomologyIso, shiftedStalkValueIso]
  have he : εC ≫ HC.map ((stalkToDerived V).app U) = (canonicalRightZeroIso V).inv.app U := rfl
  rw [hd]
  calc
    _ = ((εC ≫ HC.map ((stalkToDerived V).app U)) ≫
          (canonicalRightZeroIso V).hom.app U) ≫ V.map εB ≫ V.map (HB.map t) := by
      simp only [Category.assoc]
      rfl
    _ = _ := by
      rw [he, Iso.inv_hom_id_app]
      erw [Category.id_comp, ← V.map_comp]

open AdvancedHomologicalAlgebra.GrothendieckSpectralSequence

lemma derivedFirstEdge_degreeZeroUnit (P : Package F V) (X : A) :
    (degreeZeroUnit V).app (F.obj X) ≫ (derivedFirstEdge F V P 0).app X =
      (degreeZeroUnit (F ⋙ V)).app X := by
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let Y := (DerivedCategory.Plus.singleFunctor A 0).obj X
  let : ∀ n, IsIso ((comparisonValue F V).app n) := P.comparison_isIso
  let : IsIso (comparisonValue F V) := NatIso.isIso_of_isIso_app _
  let c := (asIso (comparisonValue F V)).app Y
  let ε := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app (V.obj (F.obj X))
  change (ε ≫ H.map ((stalkToDerived V).app (F.obj X))) ≫
      H.map (V.rightDerivedFunctorPlus.map ((stalkToDerived F).app X)) ≫ H.map c.inv =
    ε ≫ H.map ((stalkToDerived (F ⋙ V)).app X)
  rw [Category.assoc, ← H.map_comp, ← H.map_comp]
  congr 2
  rw [← reassoc_of% (stalkToDerived_comp_app F V X)]
  change (stalkToDerived (F ⋙ V)).app X ≫ c.hom ≫ c.inv = _
  rw [c.hom_inv_id]
  exact Category.comp_id _

end CompositionAtDegreeZero

section ColumnEdge

variable {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C] [EnoughInjectives B]
  (V U : B ⥤ C) [V.Additive] [U.Additive] [PreservesFiniteLimits V]

/-- Any natural comparison to a functor on cohomology commutes with the
canonical column edge if it agrees with the normalized map on stalks. -/
lemma derivedColumn_comparison (n : ℤ) (η : V ⟶ U)
    (α : V.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n ⟶
      DerivedCategory.Plus.homologyFunctor B n ⋙ U)
    (hα : ∀ X : B,
      α.app ((DerivedCategory.Plus.singleFunctor B n).obj X) ≫
        U.map ((singlePlusHomologyIso (B := B) n).hom.app X) =
      (rightDerivedStalkHomologyIso V n).hom.app X ≫ η.app X) :
    derivedTruncationEdge V n ≫ whiskerLeft (DerivedCategory.Plus.homologyFunctor B n) η = α := by
  ext Y
  let H := DerivedCategory.Plus.homologyFunctor B n
  let L := V.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let i := (t.truncLEι n).app Y
  let p := (truncationToSingle n).app Y
  let ε := (singlePlusHomologyIso (B := B) n).hom.app (H.obj Y)
  haveI : IsIso (L.map i) := isIso_homology_rightDerived_truncLEι V Y n
  have hp : H.map p ≫ ε = H.map i := truncationToSingle_normalization n Y
  change (derivedTruncationEdge V n).app Y ≫ η.app (H.obj Y) = α.app Y
  rw [← cancel_epi (L.map i)]
  have he : (derivedTruncationEdge V n).app Y =
      inv (L.map i) ≫ L.map p ≫ (rightDerivedStalkHomologyIso V n).hom.app (H.obj Y) := by
    simp only [derivedTruncationEdge, homology_rightDerived_truncLEIso,
      NatTrans.comp_app, asIso_inv, NatIso.isIso_inv_app, whiskerRight_app,
      whiskerLeft_app, associator_hom_app, isoWhiskerLeft_hom, Category.id_comp]
    rfl
  calc
    L.map i ≫ (derivedTruncationEdge V n).app Y ≫ η.app (H.obj Y) =
      L.map p ≫ α.app ((DerivedCategory.Plus.singleFunctor B n).obj (H.obj Y)) ≫ U.map ε := by
        rw [he, Category.assoc, IsIso.hom_inv_id_assoc, Category.assoc, ← hα]
    _ = α.app ((t.truncLE n).obj Y) ≫ U.map (H.map p) ≫ U.map ε := by
      have h := α.naturality p
      change L.map p ≫ α.app _ = α.app _ ≫ U.map (H.map p) at h
      rw [reassoc_of% h]
    _ = α.app ((t.truncLE n).obj Y) ≫ U.map (H.map i) := by
      rw [← U.map_comp, hp]
    _ = L.map i ≫ α.app Y := (α.naturality i).symm

lemma mappedStalkIso_natural (η : V ⟶ U) (X : B) :
    (mappedStalkIso V).hom.app X ≫
      DerivedCategory.Plus.Q.map (η.mapCochainComplexPlus.app ((stalkComplex B).obj X)) =
    (DerivedCategory.Plus.singleFunctor C 0).map (η.app X) ≫ (mappedStalkIso U).hom.app X := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp]
  simp only [mappedStalkIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.whiskeringRight_preimage_app, Functor.FullyFaithful.map_preimage, id,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    associator_inv_app, associator_hom_app, isoWhiskerRight_hom, whiskerRight_app,
    Iso.symm_hom, Category.id_comp, Category.comp_id]
  change ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app (V.obj X) ≫
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).inv.app X)) ≫
      DerivedCategory.Q.map ((η.mapHomologicalComplex (.up ℤ)).app ((CochainComplex.singleFunctor B 0).obj X)) =
    (DerivedCategory.singleFunctor C 0).map (η.app X) ≫
      ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app (U.obj X) ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).inv.app X))
  rw [Category.assoc, ← DerivedCategory.Q.map_comp,
    HomologicalComplex.natTransMapHomologicalComplex_app_single_obj,
    Iso.inv_hom_id_app_assoc, DerivedCategory.Q.map_comp, ← Category.assoc]
  have h := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality (η.app X)
  change (DerivedCategory.singleFunctor C 0).map (η.app X) ≫
    (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app (U.obj X) =
    (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app (V.obj X) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map (η.app X)) at h
  rw [← h, Category.assoc]

lemma stalkToDerived_natural (η : V ⟶ U) (X : B) :
    (stalkToDerived V).app X ≫ η.rightDerivedFunctorPlus.app ((DerivedCategory.Plus.singleFunctor B 0).obj X) =
    (DerivedCategory.Plus.singleFunctor C 0).map (η.app X) ≫ (stalkToDerived U).app X := by
  simp only [stalkToDerived, NatTrans.comp_app, whiskerLeft_app, Category.assoc]
  have h := η.rightDerivedFunctorPlus_fac_app ((stalkComplex B).obj X)
  change V.rightDerivedFunctorPlusUnit.app ((stalkComplex B).obj X) ≫
    η.rightDerivedFunctorPlus.app ((DerivedCategory.Plus.singleFunctor B 0).obj X) = _ at h
  rw [h, ← Category.assoc, mappedStalkIso_natural V U η X, Category.assoc]

lemma canonicalRightZeroIso_natural [PreservesFiniteLimits U] (η : V ⟶ U) (X : B) :
    (DerivedCategory.Plus.homologyFunctor C 0).map
        (η.rightDerivedFunctorPlus.app ((DerivedCategory.Plus.singleFunctor B 0).obj X)) ≫
      (canonicalRightZeroIso U).hom.app X =
    (canonicalRightZeroIso V).hom.app X ≫ η.app X := by
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let ε := singlePlusHomologyIso (B := C) 0
  let T := DerivedCategory.Plus.singleFunctor C 0
  let h := stalkToDerived_natural V U η X
  apply (cancel_epi ((canonicalRightZeroIso V).inv.app X)).1
  rw [Iso.inv_hom_id_app_assoc]
  have hv (W : B ⥤ C) [W.Additive] [PreservesFiniteLimits W] :
      (canonicalRightZeroIso W).inv.app X = ε.inv.app (W.obj X) ≫ H.map ((stalkToDerived W).app X) := by
    rfl
  rw [hv V, Category.assoc, ← H.map_comp_assoc, h, H.map_comp_assoc]
  have hn := ε.inv.naturality (η.app X)
  change η.app X ≫ ε.inv.app (U.obj X) = ε.inv.app (V.obj X) ≫ H.map (T.map (η.app X)) at hn
  rw [← Category.assoc (ε.inv.app (V.obj X)), ← hn, Category.assoc, ← reassoc_of% (hv U)]
  rw [Iso.inv_hom_id_app, Category.comp_id]

/-- The degree shift used by the Grothendieck column edge is natural in the
coefficient functor. -/
lemma shiftedStalkValueIso_natural (η : V ⟶ U) (n : ℤ) (X : B) :
    (DerivedCategory.Plus.homologyFunctor C n).map
        (η.rightDerivedFunctorPlus.app ((DerivedCategory.Plus.singleFunctor B n).obj X)) ≫
      (shiftedStalkValueIso U n).hom.app X =
    (shiftedStalkValueIso V n).hom.app X ≫
      (DerivedCategory.Plus.homologyFunctor C 0).map
        (η.rightDerivedFunctorPlus.app ((DerivedCategory.Plus.singleFunctor B 0).obj X)) := by
  by_cases hn : n = 0
  · subst n
    simp [shiftedStalkValueIso]
  simp only [shiftedStalkValueIso, dite_eq_right hn, id, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom, Category.assoc]
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let Y := (DerivedCategory.Plus.singleFunctor B n).obj X
  let e := ((DerivedCategory.Plus.singleFunctors B).shiftIso n 0 n (by omega)).hom.app X
  let τ := η.rightDerivedFunctorPlus
  change (H.shift n).map (τ.app Y) ≫ (H.isoShift n).inv.app (U.rightDerivedFunctorPlus.obj Y) ≫
    H.map ((U.rightDerivedFunctorPlus.commShiftIso n).inv.app Y) ≫
    H.map (U.rightDerivedFunctorPlus.map e) =
      (H.isoShift n).inv.app (V.rightDerivedFunctorPlus.obj Y) ≫
        H.map ((V.rightDerivedFunctorPlus.commShiftIso n).inv.app Y) ≫
        H.map (V.rightDerivedFunctorPlus.map e) ≫ H.map (τ.app _)
  rw [reassoc_of% ((H.isoShift n).inv.naturality (τ.app Y))]
  change (H.isoShift n).inv.app (V.rightDerivedFunctorPlus.obj Y) ≫
      H.map ((τ.app Y)⟦n⟧') ≫ H.map ((U.rightDerivedFunctorPlus.commShiftIso n).inv.app Y) ≫
        H.map (U.rightDerivedFunctorPlus.map e) = _
  simp only [← H.map_comp]
  congr 2
  rw [NatTrans.shift_app, Category.assoc,
    Category.assoc (τ.app (Y⟦n⟧)), Iso.hom_inv_id_app_assoc]
  have he := τ.naturality e
  change V.rightDerivedFunctorPlus.map e ≫ τ.app ((DerivedCategory.Plus.singleFunctor B 0).obj X) =
    τ.app (Y⟦n⟧) ≫ U.rightDerivedFunctorPlus.map e at he
  rw [← he]

lemma derivedColumn_natural [PreservesFiniteLimits U] (η : V ⟶ U) (n : ℤ) :
    derivedTruncationEdge V n ≫ whiskerLeft (DerivedCategory.Plus.homologyFunctor B n) η =
    whiskerRight η.rightDerivedFunctorPlus (DerivedCategory.Plus.homologyFunctor C n) ≫
      derivedTruncationEdge U n := by
  apply derivedColumn_comparison V U n η
  intro X
  simp only [NatTrans.comp_app, whiskerRight_app, derivedTruncationEdge_app_stalk,
    Category.assoc, ← Functor.map_comp, ← Iso.app_hom, Iso.inv_hom_id,
    rightDerivedStalkHomologyIso, Iso.trans_hom]
  rw [U.map_id, Category.comp_id]
  simp only [Iso.app_hom]
  rw [reassoc_of% (shiftedStalkValueIso_natural V U η n X),
    ← Category.assoc ((shiftedStalkValueIso V n).hom.app X),
    Category.assoc ((shiftedStalkValueIso V n).hom.app X), canonicalRightZeroIso_natural V U η X]

section ExactFunctor

variable [PreservesFiniteLimits U] [PreservesFiniteColimits U]

private lemma exact_derived_unit_isIso (K : CochainComplex.Plus B) :
    IsIso (U.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨b, hb⟩ := K.property
  letI := hb
  obtain ⟨I, _, f, hf⟩ := CochainComplex.Plus.exists_quasiIso_injective K b
  haveI : IsIso (DerivedCategory.Plus.Q.map f) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso B) f hf
  haveI : QuasiIso f.hom := hf
  haveI : IsIso (DerivedCategory.Plus.Q.map (U.mapCochainComplexPlus.map f)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso C) _
      (show QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map f.hom) from inferInstance)
  have h := U.rightDerivedFunctorPlusUnit.naturality f
  dsimp only [Functor.comp_map] at h
  haveI : IsIso (U.rightDerivedFunctorPlusUnit.app K ≫
      U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f))

private def complexHomologyIso (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) n :=
  isoWhiskerLeft (CochainComplex.Plus.ι C) (DerivedCategory.homologyFunctorFactors C n)

private def mappedHomologyIso (n : ℤ) :
    U.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) n ≅
      CochainComplex.Plus.ι B ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) n ⋙ U :=
  NatIso.ofComponents (fun K => (K.obj.sc n).mapHomologyIso U)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor B (.up ℤ) n).map f.hom) U)

private def exactHomologyIso (n : ℤ) :
    U.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      DerivedCategory.Plus.homologyFunctor B n ⋙ U := by
  let Q := DerivedCategory.Plus.Q (C := B)
  let W := CochainComplex.Plus.quasiIso B
  let H := DerivedCategory.Plus.homologyFunctor C n
  let HU := DerivedCategory.Plus.homologyFunctor B n ⋙ U
  letI (K : CochainComplex.Plus B) : IsIso (U.rightDerivedFunctorPlusUnit.app K) :=
    exact_derived_unit_isIso U K
  letI : IsIso U.rightDerivedFunctorPlusUnit := NatIso.isIso_of_isIso_app _
  let e : Q ⋙ U.rightDerivedFunctorPlus ⋙ H ≅
      U.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) n :=
    (associator _ _ _).symm ≪≫ isoWhiskerRight (asIso U.rightDerivedFunctorPlusUnit).symm H ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (complexHomologyIso (C := C) n)
  let e' : Q ⋙ HU ≅
      CochainComplex.Plus.ι B ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) n ⋙ U :=
    (associator _ _ _).symm ≪≫ isoWhiskerRight (complexHomologyIso (C := B) n) U ≪≫ associator _ _ _
  letI : Localization.Lifting Q W _ _ := ⟨e⟩
  letI : Localization.Lifting Q W _ _ := ⟨e'⟩
  exact Localization.liftNatIso Q W _ _ _ _ (mappedHomologyIso U n)

private lemma exactHomologyIso_on_complex (n : ℤ) (K : CochainComplex.Plus B) :
    (DerivedCategory.Plus.homologyFunctor C n).map (U.rightDerivedFunctorPlusUnit.app K) ≫
      (exactHomologyIso U n).hom.app (DerivedCategory.Plus.Q.obj K) =
    (complexHomologyIso (C := C) n).hom.app (U.mapCochainComplexPlus.obj K) ≫
      ((K.obj.sc n).mapHomologyIso U).hom ≫
      U.map ((complexHomologyIso (C := B) n).inv.app K) := by
  simp only [exactHomologyIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.iso, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    associator_hom_app, associator_inv_app, Category.assoc, Category.id_comp,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerRight_inv, isoWhiskerLeft_hom,
    whiskerLeft_app, Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app, ← Functor.map_comp_assoc,
    IsIso.hom_inv_id, mappedHomologyIso, NatIso.ofComponents_hom_app]
  simp

open HomologicalComplex in
private abbrev exactMapComplex := U.mapHomologicalComplex (.up ℤ)

open HomologicalComplex in
private lemma shiftShortComplex_map (K : CochainComplex B ℤ) (n i j : ℤ) (h : n + i = j) :
    (shortComplexFunctor C (.up ℤ) i).map (((exactMapComplex U).commShiftIso n).hom.app K) ≫
      (CochainComplex.shiftShortComplexFunctorIso C n i j h).hom.app ((exactMapComplex U).obj K) =
    U.mapShortComplex.map ((CochainComplex.shiftShortComplexFunctorIso B n i j h).hom.app K) := by
  ext <;> simp [CochainComplex.shiftShortComplexFunctorIso, CochainComplex.shiftShortComplexFunctor',
    CochainComplex.shiftEval, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    Functor.map_units_smul, XIsoOfEq, eqToHom_map]

open HomologicalComplex in
private lemma exactMapHomologyShift (K : CochainComplex B ℤ) (n i j : ℤ) (h : n + i = j) :
    (homologyFunctor C (.up ℤ) 0).shiftMap (((exactMapComplex U).commShiftIso n).hom.app K) i j h ≫
      ((K.sc j).mapHomologyIso U).hom =
    (((K⟦n⟧).sc i).mapHomologyIso U).hom ≫
      U.map (((homologyFunctor B (.up ℤ) 0).shiftIso n i j h).hom.app K) := by
  simp only [Functor.shiftMap]
  change (_ ≫ (CochainComplex.ShiftSequence.shiftIso C n i j h).hom.app ((exactMapComplex U).obj K)) ≫ _ =
    _ ≫ U.map ((CochainComplex.ShiftSequence.shiftIso B n i j h).hom.app K)
  simp only [CochainComplex.ShiftSequence.shiftIso_hom_app]
  change (ShortComplex.homologyMap ((shortComplexFunctor C (.up ℤ) i).map
        (((exactMapComplex U).commShiftIso n).hom.app K)) ≫
      ShortComplex.homologyMap ((CochainComplex.shiftShortComplexFunctorIso C n i j h).hom.app
        ((exactMapComplex U).obj K))) ≫ _ = _
  rw [← ShortComplex.homologyMap_comp, shiftShortComplex_map U K n i j h]
  exact ShortComplex.mapHomologyIso_hom_naturality _ U

open HomologicalComplex in
open HomologicalComplex in
private lemma exactMapHomologyShiftMap {K L : CochainComplex B ℤ} {n : ℤ} (f : K ⟶ L⟦n⟧)
    (i j : ℤ) (h : n + i = j) :
    (homologyFunctor C (.up ℤ) 0).shiftMap (ShiftedHom.map f (exactMapComplex U)) i j h ≫
      ((L.sc j).mapHomologyIso U).hom =
    ((K.sc i).mapHomologyIso U).hom ≫
      U.map ((homologyFunctor B (.up ℤ) 0).shiftMap f i j h) := by
  rw [ShiftedHom.map, Functor.shiftMap_comp', Category.assoc, exactMapHomologyShift U L n i j h]
  have hf := ShortComplex.mapHomologyIso_hom_naturality ((shortComplexFunctor B (.up ℤ) i).map f) U
  change (homologyFunctor C (.up ℤ) i).map ((exactMapComplex U).map f) ≫
      (((L⟦n⟧).sc i).mapHomologyIso U).hom =
    ((K.sc i).mapHomologyIso U).hom ≫ U.map ((homologyFunctor B (.up ℤ) i).map f) at hf
  change (homologyFunctor C (.up ℤ) i).map ((exactMapComplex U).map f) ≫
      (((L⟦n⟧).sc i).mapHomologyIso U).hom ≫ _ = _
  rw [reassoc_of% hf, ← U.map_comp]
  rfl

private lemma mapHomologyIso_homologyπ (S : ShortComplex B) :
    (S.map U).homologyπ ≫ (S.mapHomologyIso U).hom =
      (S.mapCyclesIso U).hom ≫ U.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq U, h.mapCyclesIso_eq U]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    (h.map U).homologyπ_comp_homologyIso_hom_assoc, ← U.map_comp]
  congr 1
  change U.map h.π ≫ U.map h.homologyIso.inv = _
  rw [← U.map_comp, h.π_comp_homologyIso_inv]

private lemma mapSingleHomologyExact (n : ℤ) (X : B) :
    HomologicalComplex.homologyMap
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) n).inv.app X) n ≫
      ((((CochainComplex.singleFunctor B n).obj X).sc n).mapHomologyIso U).hom ≫
      U.map (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n X).hom =
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n (U.obj X)).hom := by
  let K := (CochainComplex.singleFunctor B n).obj X
  let L := (CochainComplex.singleFunctor C n).obj (U.obj X)
  let f : L ⟶ (exactMapComplex U).obj K :=
    (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) n).inv.app X
  apply (cancel_epi (L.homologyπ n)).1
  rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom, ← Category.assoc,
    HomologicalComplex.homologyπ_naturality, Category.assoc]
  change HomologicalComplex.cyclesMap f n ≫ ((K.sc n).map U).homologyπ ≫
    ((K.sc n).mapHomologyIso U).hom ≫ U.map (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n X).hom = _
  rw [reassoc_of% (mapHomologyIso_homologyπ U (K.sc n)), ← U.map_comp]
  change HomologicalComplex.cyclesMap f n ≫ ((K.sc n).mapCyclesIso U).hom ≫ U.map (K.homologyπ n ≫ (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n X).hom) = _
  unfold K
  rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  simp only [HomologicalComplex.singleObjCyclesSelfIso_hom, U.map_comp]
  have hc := (K.sc n).mapCyclesIso_hom_iCycles_assoc U
    (U.map (HomologicalComplex.singleObjXSelf (.up ℤ) n X).hom)
  change _ ≫ U.map (K.iCycles n) ≫ _ = _ at hc
  rw [hc]
  change (HomologicalComplex.cyclesMap f n) ≫ ((exactMapComplex U).obj K).iCycles n ≫ _ = _
  rw [HomologicalComplex.cyclesMap_i_assoc]
  simp [f, L,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Category.assoc, ← U.map_comp]

private lemma exactHomologyIso_stalk_zero (X : B) :
    (exactHomologyIso U 0).hom.app ((DerivedCategory.Plus.singleFunctor B 0).obj X) ≫
      U.map ((singlePlusHomologyIso (B := B) 0).hom.app X) =
    (canonicalRightZeroIso U).hom.app X := by
  let K := (stalkComplex B).obj X
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let e := singlePlusHomologyIso (B := C) 0
  let f := (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).inv.app X
  have hv : (canonicalRightZeroIso U).inv.app X =
      e.inv.app (U.obj X) ≫ H.map ((stalkToDerived U).app X) := rfl
  apply (cancel_epi ((canonicalRightZeroIso U).inv.app X)).1
  rw [Iso.inv_hom_id_app, hv]
  simp only [stalkToDerived, NatTrans.comp_app, whiskerLeft_app, Functor.map_comp, Category.assoc]
  have h := exactHomologyIso_on_complex U 0 K
  change H.map (U.rightDerivedFunctorPlusUnit.app K) ≫
    (exactHomologyIso U 0).hom.app ((DerivedCategory.Plus.singleFunctor B 0).obj X) = _ at h
  rw [reassoc_of% h]
  have hfos : DerivedCategory.Plus.ι.map ((mappedStalkIso U).hom.app X) = DerivedCategory.Q.map f := by
    simp only [mappedStalkIso, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.whiskeringRight_preimage_app, Functor.FullyFaithful.map_preimage, id,
      Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
      associator_inv_app, associator_hom_app, isoWhiskerRight_hom, whiskerRight_app,
      Iso.symm_hom, Category.id_comp, Category.comp_id, f, DerivedCategory.singleFunctorIsoCompQ_hom_app]
    exact Category.id_comp _
  change e.inv.app (U.obj X) ≫ (DerivedCategory.homologyFunctor C 0).map
    (DerivedCategory.Plus.ι.map ((mappedStalkIso U).hom.app X)) ≫ _ = _
  rw [hfos]
  rw [show (complexHomologyIso (C := C) 0).hom.app (U.mapCochainComplexPlus.obj K) =
      (DerivedCategory.homologyFunctorFactors C 0).hom.app
        ((U.mapHomologicalComplex (.up ℤ)).obj K.obj) from rfl]
  have hn := DerivedCategory.homologyFunctorFactors_hom_naturality f 0
  change _ ≫ (DerivedCategory.homologyFunctorFactors C 0).hom.app
    ((U.mapHomologicalComplex (.up ℤ)).obj K.obj) = _ at hn
  rw [reassoc_of% hn]
  have hs1 : (singlePlusHomologyIso (B := C) 0).hom.app (U.obj X) =
      (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (U.obj X)).hom := by
    simp [singlePlusHomologyIso, DerivedCategory.singleFunctorCompHomologyFunctorIso]
    exact Category.id_comp _
  have hs2 : (singlePlusHomologyIso (B := B) 0).hom.app X =
      (complexHomologyIso (C := B) 0).hom.app K ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 X).hom := by
    simp [singlePlusHomologyIso, DerivedCategory.singleFunctorCompHomologyFunctorIso, complexHomologyIso, K]
    exact Category.id_comp _
  rw [hs2, ← U.map_comp, Iso.inv_hom_id_app_assoc]
  have hm := mapSingleHomologyExact U 0 X
  change HomologicalComplex.homologyMap f 0 ≫ (((K.obj).sc 0).mapHomologyIso U).hom ≫
    U.map (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 X).hom = _ at hm
  rw [hm]
  rw [← hs1, Iso.inv_hom_id_app]
  rfl

private lemma plusHomologyShiftMapQ {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    {K L : CochainComplex.Plus D} {n : ℤ} (f : ShiftedHom K L n) (i j : ℤ) (h : n + i = j) :
    (DerivedCategory.Plus.homologyFunctor D 0).shiftMap (f.map DerivedCategory.Plus.Q) i j h =
    (complexHomologyIso (C := D) i).hom.app K ≫
      (HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftMap (f.map (CochainComplex.Plus.ι D)) i j h ≫
      (complexHomologyIso (C := D) j).inv.app L := by
  have hs := ShiftedHom.map_naturality_1 f (DerivedCategory.Plus.QCompιIso D)
  simp only [DerivedCategory.Plus.QCompιIso_inv_app, DerivedCategory.Plus.QCompιIso_hom_app,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] at hs
  have hs' : (f.map DerivedCategory.Plus.Q).map DerivedCategory.Plus.ι =
      (f.map (CochainComplex.Plus.ι D)).map DerivedCategory.Q := by
    erw [(shiftFunctor (DerivedCategory D) n).map_id, Category.comp_id, Category.id_comp] at hs
    exact hs
  have heq {X Y : DerivedCategory.Plus D} (g : ShiftedHom X Y n) :
      (DerivedCategory.Plus.homologyFunctor D 0).shiftMap g i j h =
      (DerivedCategory.homologyFunctor D 0).shiftMap (g.map DerivedCategory.Plus.ι) i j h := by
    simp [Functor.shiftMap, DerivedCategory.Plus.homologyFunctor, Functor.shiftIso, ShiftedHom.map]
    change ((DerivedCategory.homologyFunctor D 0).shift i).map g.hom ≫ _ = _
    erw [Category.id_comp, ← Functor.map_comp_assoc]
  rw [heq, hs', DerivedCategory.shiftMap_homologyFunctor_map_Q (f.map (CochainComplex.Plus.ι D)) i j h]
  rfl

private lemma exactMapComplexShift_ι {K L : CochainComplex.Plus B} {n : ℤ} (f : ShiftedHom K L n) :
    (f.map U.mapCochainComplexPlus).map (CochainComplex.Plus.ι C) =
    (f.map (CochainComplex.Plus.ι B)).map (exactMapComplex U) := by
  have hs := ShiftedHom.map_naturality_1 f U.mapCochainComplexPlusCompι
  simp only [Functor.mapCochainComplexPlusCompι_inv_app, Functor.mapCochainComplexPlusCompι_hom_app,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] at hs
  erw [(shiftFunctor (CochainComplex C ℤ) n).map_id, Category.comp_id, Category.id_comp] at hs
  exact hs

private lemma exactHomologyShiftMapQ {K L : CochainComplex.Plus B} {n : ℤ}
    (f : ShiftedHom K L n) (i j : ℤ) (h : n + i = j) :
    (DerivedCategory.Plus.homologyFunctor C 0).shiftMap
        ((f.map DerivedCategory.Plus.Q).map U.rightDerivedFunctorPlus) i j h ≫
      (exactHomologyIso U j).hom.app (DerivedCategory.Plus.Q.obj L) =
    (exactHomologyIso U i).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      U.map ((DerivedCategory.Plus.homologyFunctor B 0).shiftMap (f.map DerivedCategory.Plus.Q) i j h) := by
  let Q := DerivedCategory.Plus.Q (C := B)
  let FU := U.mapCochainComplexPlus
  let η := U.rightDerivedFunctorPlusUnit
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let Hi := DerivedCategory.Plus.homologyFunctor C i
  let Hj := DerivedCategory.Plus.homologyFunctor C j
  let X := Q.obj K
  let Y := Q.obj L
  let a := f.map (FU ⋙ DerivedCategory.Plus.Q)
  let b := f.map (Q ⋙ U.rightDerivedFunctorPlus)
  have hb := ShiftedHom.map_naturality f η
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hb
  change a ≫ (η.app L)⟦n⟧' = η.app K ≫ b at hb
  have hinj : IsIso (Hi.map (η.app K)) := by
    haveI := exact_derived_unit_isIso U K
    infer_instance
  apply (cancel_epi (Hi.map (η.app K))).1
  have hh : Hi.map (η.app K) ≫ H.shiftMap b i j h =
      H.shiftMap a i j h ≫ Hj.map (η.app L) := by
    have h' := congrArg (fun f => H.shiftMap f i j h) hb
    rw [H.shiftMap_comp a (η.app L) i j h, H.shiftMap_comp' (η.app K) b i j h] at h'
    exact h'.symm
  rw [← ShiftedHom.comp_map f Q U.rightDerivedFunctorPlus]
  change Hi.map (η.app K) ≫ H.shiftMap b i j h ≫ (exactHomologyIso U j).hom.app Y = _
  rw [reassoc_of% hh, exactHomologyIso_on_complex U j L, reassoc_of% (exactHomologyIso_on_complex U i K)]
  dsimp only [a, FU, Q]
  rw [ShiftedHom.comp_map, plusHomologyShiftMapQ, plusHomologyShiftMapQ, exactMapComplexShift_ι,
    Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hmap := exactMapHomologyShiftMap U (f.map (CochainComplex.Plus.ι B)) i j h
  change _ ≫ ((L.obj.sc j).mapHomologyIso U).hom = ((K.obj.sc i).mapHomologyIso U).hom ≫ _ at hmap
  rw [← Category.assoc _ ((L.obj.sc j).mapHomologyIso U).hom, hmap]
  simp only [Category.assoc, ← U.map_comp, Iso.inv_hom_id_app_assoc]

lemma exactHomologyShift (X : DerivedCategory.Plus B) (n i j : ℤ) (h : n+i = j) :
    ((DerivedCategory.Plus.homologyFunctor C 0).shift i).map ((U.rightDerivedFunctorPlus.commShiftIso n).hom.app X) ≫
        ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso n i j h).hom.app (U.rightDerivedFunctorPlus.obj X) ≫
        (exactHomologyIso U j).hom.app X =
      (exactHomologyIso U i).hom.app (X⟦n⟧) ≫
        U.map (((DerivedCategory.Plus.homologyFunctor B 0).shiftIso n i j h).hom.app X) := by
  let FU := U.rightDerivedFunctorPlus
  let HC := DerivedCategory.Plus.homologyFunctor C 0
  let HB := DerivedCategory.Plus.homologyFunctor B 0
  let l : shiftFunctor (DerivedCategory.Plus B) n ⋙ FU ⋙ HC.shift i ⟶ HB.shift j ⋙ U :=
    (Functor.associator _ _ _).inv ≫ whiskerRight (FU.commShiftIso n).hom (HC.shift i) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft FU (HC.shiftIso n i j h).hom ≫
      (exactHomologyIso U j).hom
  let r : shiftFunctor (DerivedCategory.Plus B) n ⋙ FU ⋙ HC.shift i ⟶ HB.shift j ⋙ U :=
    whiskerLeft _ (exactHomologyIso U i).hom ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight (HB.shiftIso n i j h).hom U
  suffices hlr : l = r by
    simpa only [l, r, NatTrans.comp_app, associator_hom_app, associator_inv_app,
      whiskerRight_app, whiskerLeft_app, Category.id_comp, Category.assoc] using congrArg (fun T => T.app X) hlr
  apply Localization.natTrans_ext (DerivedCategory.Plus.Q (C := B)) (CochainComplex.Plus.quasiIso B)
  intro K
  let Q := DerivedCategory.Plus.Q (C := B)
  let T := Q.obj K
  let W := (Q.commShiftIso n).hom.app K
  let f : ShiftedHom (K⟦n⟧) K n := 𝟙 _
  have hf : f.map Q = W := by
    dsimp only [f, W, ShiftedHom.map]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have he := exactHomologyShiftMapQ U f i j h
  rw [hf] at he
  simp only [l, r, NatTrans.comp_app, associator_hom_app, associator_inv_app,
    whiskerRight_app, whiskerLeft_app, Category.id_comp]
  change _ ≫ _ ≫ (exactHomologyIso U j).hom.app T =
    (exactHomologyIso U i).hom.app (T⟦n⟧) ≫ _ 
  apply (cancel_epi ((FU ⋙ HC.shift i).map W)).mp
  change (HC.shift i).map (FU.map W) ≫ (HC.shift i).map ((FU.commShiftIso n).hom.app T) ≫
      _ ≫ (exactHomologyIso U j).hom.app T = _
  rw [← CategoryTheory.Functor.map_comp_assoc]
  rw [← Category.assoc ((HC.shift i).map (FU.map W ≫ (FU.commShiftIso n).hom.app T))]
  change HC.shiftMap (ShiftedHom.map W FU) i j h ≫ (exactHomologyIso U j).hom.app T = _
  rw [he]
  have hn := (exactHomologyIso U i).hom.naturality W
  change (HC.shift i).map (FU.map W) ≫ (exactHomologyIso U i).hom.app (T⟦n⟧) =
    (exactHomologyIso U i).hom.app (Q.obj (K⟦n⟧)) ≫ U.map ((HB.shift i).map W) at hn
  change (exactHomologyIso U i).hom.app (Q.obj (K⟦n⟧)) ≫
      U.map ((HB.shift i).map W ≫ (HB.shiftIso n i j h).hom.app T) =
    (HC.shift i).map (FU.map W) ≫ (exactHomologyIso U i).hom.app (T⟦n⟧) ≫
      U.map ((HB.shiftIso n i j h).hom.app T)
  rw [reassoc_of% hn, ← CategoryTheory.Functor.map_comp]

lemma exactHomologyIso_shiftMap {X Y : DerivedCategory.Plus B} {n : ℤ}
    (f : ShiftedHom X Y n) (i j : ℤ) (h : n+i = j) :
    (DerivedCategory.Plus.homologyFunctor C 0).shiftMap (f.map U.rightDerivedFunctorPlus) i j h ≫
      (exactHomologyIso U j).hom.app Y =
    (exactHomologyIso U i).hom.app X ≫
      U.map ((DerivedCategory.Plus.homologyFunctor B 0).shiftMap f i j h) := by
  let FU := U.rightDerivedFunctorPlus
  let HC := DerivedCategory.Plus.homologyFunctor C 0
  let HB := DerivedCategory.Plus.homologyFunctor B 0
  dsimp only [Functor.shiftMap, ShiftedHom.map]
  rw [Category.assoc]
  change (HC.shift i).map (FU.map f ≫ (FU.commShiftIso n).hom.app Y) ≫
    (HC.shiftIso n i j h).hom.app (FU.obj Y) ≫ (exactHomologyIso U j).hom.app Y =
    (exactHomologyIso U i).hom.app X ≫ U.map
      ((HB.shift i).map f ≫ (HB.shiftIso n i j h).hom.app Y)
  rw [CategoryTheory.Functor.map_comp, Category.assoc, exactHomologyShift U Y n i j h]
  have hn := (exactHomologyIso U i).hom.naturality f
  change (HC.shift i).map (FU.map f) ≫ (exactHomologyIso U i).hom.app (Y⟦n⟧) =
    (exactHomologyIso U i).hom.app X ≫ U.map ((HB.shift i).map f) at hn
  rw [reassoc_of% hn, ← CategoryTheory.Functor.map_comp]


private lemma singleHomologyShiftMap {D : Type*} [Category* D] [Abelian D] (n : ℤ) (X : D) :
    (HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftMap
      (((CochainComplex.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X) 0 n (add_zero n) ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n X).hom =
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 X).hom := by
  let K := (CochainComplex.singleFunctor D 0).obj X
  let L := (CochainComplex.singleFunctor D n).obj X
  let e : K ⟶ L⟦n⟧ := ((CochainComplex.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X
  let f : K.sc 0 ⟶ L.sc n :=
    (HomologicalComplex.shortComplexFunctor D (.up ℤ) 0).map e ≫
      (CochainComplex.shiftShortComplexFunctorIso D n 0 n (add_zero n)).hom.app L
  change (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor D (.up ℤ) 0).map e) ≫
      (CochainComplex.ShiftSequence.shiftIso D n 0 n (add_zero n)).hom.app L) ≫ _ = _
  rw [CochainComplex.ShiftSequence.shiftIso_hom_app, ← ShortComplex.homologyMap_comp]
  change ShortComplex.homologyMap f ≫ _ = _
  apply (cancel_epi (K.homologyπ 0)).1
  have h0 : K.homologyπ 0 ≫ (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 X).hom =
      K.iCycles 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom  := by exact (HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom _ _ _).trans rfl
  have hn : L.homologyπ n ≫ (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n X).hom =
      L.iCycles n ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) n X).hom  := by exact (HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom _ _ _).trans rfl
  have hp := ShortComplex.homologyπ_naturality f
  change K.homologyπ 0 ≫ ShortComplex.homologyMap f = ShortComplex.cyclesMap f ≫ L.homologyπ n at hp
  rw [h0, ← Category.assoc, hp, Category.assoc, hn]
  have hc := (ShortComplex.cyclesMap_i f)
  change ShortComplex.cyclesMap f ≫ L.iCycles n = K.iCycles 0 ≫ f.τ₂ at hc
  rw [reassoc_of% hc]
  have hk : f.τ₂ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) n X).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom := by
    simp [f, e, L, CochainComplex.singleFunctors, CochainComplex.shiftShortComplexFunctorIso,
      CochainComplex.shiftShortComplexFunctor', CochainComplex.shiftEval,
      HomologicalComplex.XIsoOfEq, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToHom_trans]
    rfl
  rw [hk]

private def stalkComplexInDegree {D : Type*} [Category* D] [Abelian D] (n : ℤ) (X : D) :
    CochainComplex.Plus D := ⟨(CochainComplex.singleFunctor D n).obj X, n, inferInstance⟩

private def stalkShiftedMap {D : Type*} [Category* D] [Abelian D] (n : ℤ) (X : D) :
    ShiftedHom (stalkComplexInDegree 0 X) (stalkComplexInDegree n X) n :=
  (Functor.FullyFaithful.ofFullyFaithful (CochainComplex.Plus.ι D)).preimage
    (((CochainComplex.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X ≫
      ((CochainComplex.Plus.ι D).commShiftIso n).inv.app (stalkComplexInDegree n X))

private lemma stalkShiftedMap_ι {D : Type*} [Category* D] [Abelian D] (n : ℤ) (X : D) :
    (stalkShiftedMap n X).map (CochainComplex.Plus.ι D) =
      ((CochainComplex.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X := by
  simp only [ShiftedHom.map, stalkShiftedMap, Functor.FullyFaithful.map_preimage,
    Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private lemma stalkShiftedMap_Q {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (n : ℤ) (X : D) :
    (stalkShiftedMap n X).map DerivedCategory.Plus.Q =
      ((DerivedCategory.Plus.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X := by
  let Q := DerivedCategory.Plus.Q (C := D)
  let J := DerivedCategory.Plus.ι (C := D)
  let f := stalkShiftedMap n X
  let α := (DerivedCategory.Plus.singleFunctors D).shiftIso n 0 n (add_zero n)
  let β := (DerivedCategory.singleFunctors D).shiftIso n 0 n (add_zero n)
  have hα : J.map (α.hom.app X) = (J.commShiftIso n).hom.app _ ≫ β.hom.app X := by
    dsimp only [α, DerivedCategory.Plus.singleFunctors]
    rw [SingleFunctors.map_lift_shiftIso_hom_app]
    simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [(shiftFunctor (DerivedCategory D) n).map_id, Category.id_comp, Category.comp_id]
    rfl
  apply J.map_injective
  apply (cancel_mono ((J.commShiftIso n).hom.app ((DerivedCategory.Plus.singleFunctor D n).obj X) ≫ β.hom.app X)).1
  change J.map (f.map Q) ≫ (J.commShiftIso n).hom.app _ ≫ β.hom.app X =
    J.map (α.inv.app X) ≫ (J.commShiftIso n).hom.app _ ≫ β.hom.app X
  have hαi : J.map (α.inv.app X) ≫ (J.commShiftIso n).hom.app _ ≫ β.hom.app X =
      𝟙 (J.obj ((DerivedCategory.Plus.singleFunctor D 0).obj X)) := by
    rw [← hα, ← J.map_comp, Iso.inv_hom_id_app, J.map_id]
  rw [hαi]
  have hs := ShiftedHom.map_naturality_1 f (DerivedCategory.Plus.QCompιIso D)
  simp only [DerivedCategory.Plus.QCompιIso_inv_app, DerivedCategory.Plus.QCompιIso_hom_app,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] at hs
  erw [(shiftFunctor (DerivedCategory D) n).map_id, Category.comp_id, Category.id_comp] at hs
  rw [← Category.assoc]
  have hf : ((f.map Q).map J) = J.map (f.map Q) ≫
    (J.commShiftIso n).hom.app (Q.obj (stalkComplexInDegree n X)) := rfl
  rw [← hf]
  rw [hs, stalkShiftedMap_ι]
  change ((DerivedCategory.Q).map (((CochainComplex.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X) ≫
    (DerivedCategory.Q.commShiftIso n).hom.app _) ≫ β.hom.app X = _
  simp only [β, DerivedCategory.singleFunctors, SingleFunctors.postcomp_shiftIso_hom_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id_app,
    DerivedCategory.Q.map_id]
  rfl

private lemma singlePlusHomologyIso_formula {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (n : ℤ) (X : D) :
    (singlePlusHomologyIso (B := D) n).hom.app X =
      (complexHomologyIso (C := D) n).hom.app (stalkComplexInDegree n X) ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n X).hom := by
  simp [singlePlusHomologyIso, DerivedCategory.singleFunctorCompHomologyFunctorIso,
    complexHomologyIso, stalkComplexInDegree]
  exact Category.id_comp _

private lemma singlePlusHomologyShiftMap {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (n : ℤ) (X : D) :
    (DerivedCategory.Plus.homologyFunctor D 0).shiftMap
      ((stalkShiftedMap n X).map DerivedCategory.Plus.Q) 0 n (add_zero n) ≫
      (singlePlusHomologyIso (B := D) n).hom.app X =
    (singlePlusHomologyIso (B := D) 0).hom.app X := by
  rw [plusHomologyShiftMapQ, stalkShiftedMap_ι, singlePlusHomologyIso_formula n X,
    Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [singleHomologyShiftMap n X, singlePlusHomologyIso_formula 0 X]

private lemma plus_homology_isoShiftZero {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (Y : DerivedCategory.Plus D) :
    ((DerivedCategory.Plus.homologyFunctor D 0).isoShiftZero ℤ).hom.app Y = 𝟙 _ := by
  let H := DerivedCategory.homologyFunctor D 0
  let P := HomotopyCategory.homologyFunctor D (.up ℤ) 0
  have hp (K : HomotopyCategory D (.up ℤ)) : (P.isoShiftZero ℤ).hom.app K = 𝟙 _ := by
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    have he := Functor.ShiftSequence.induced_isoShiftZero_hom_app_obj
      (HomotopyCategory.homologyFunctorFactors D (.up ℤ) 0) ℤ
      (HomotopyCategory.homologyFunctor D (.up ℤ))
      (HomotopyCategory.homologyFunctorFactors D (.up ℤ)) L
    change (P.isoShiftZero ℤ).hom.app ((HomotopyCategory.quotient D (.up ℤ)).obj L) = _ at he
    rw [he]
    change (HomotopyCategory.homologyFunctorFactors D (.up ℤ) 0).hom.app L ≫
      𝟙 _ ≫ (HomotopyCategory.homologyFunctorFactors D (.up ℤ) 0).inv.app L = _
    erw [Category.id_comp, Iso.hom_inv_id_app]
    rfl
  have hh (K : HomotopyCategory D (.up ℤ)) :
      (H.isoShiftZero ℤ).hom.app (DerivedCategory.Qh.obj K) = 𝟙 _ := by
    have he := Functor.ShiftSequence.induced_isoShiftZero_hom_app_obj
      (DerivedCategory.homologyFunctorFactorsh D 0) ℤ (DerivedCategory.homologyFunctor D)
      (DerivedCategory.homologyFunctorFactorsh D) K
    change (H.isoShiftZero ℤ).hom.app (DerivedCategory.Qh.obj K) = _ at he
    rw [he, hp]
    erw [Category.id_comp, Iso.hom_inv_id_app]
    rfl
  let J := DerivedCategory.Plus.ι (C := D)
  let X := J.obj Y
  let K := DerivedCategory.Qh.objPreimage X
  let e := DerivedCategory.Qh.objObjPreimageIso X
  have he := (H.isoShiftZero ℤ).hom.naturality e.hom
  change H.map e.hom ≫ (H.isoShiftZero ℤ).hom.app X =
      (H.isoShiftZero ℤ).hom.app (DerivedCategory.Qh.obj K) ≫ H.map e.hom at he
  rw [hh, Category.id_comp] at he
  have hX : (H.isoShiftZero ℤ).hom.app X = 𝟙 _ := by
    apply (cancel_epi (H.map e.hom)).1
    erw [Category.comp_id]
    exact he
  change (H.isoShiftZero ℤ).hom.app X ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id, hX]

private lemma shiftedStalkValueIso_inv_shiftMap (n : ℤ) (hn : n ≠ 0) (X : B) :
    (shiftedStalkValueIso U n).inv.app X =
    (DerivedCategory.Plus.homologyFunctor C 0).shiftMap
      (ShiftedHom.map (((DerivedCategory.Plus.singleFunctors B).shiftIso n 0 n (add_zero n)).inv.app X)
        U.rightDerivedFunctorPlus) 0 n (add_zero n) := by
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let R := U.rightDerivedFunctorPlus
  let Y := (DerivedCategory.Plus.singleFunctor B n).obj X
  let e := ((DerivedCategory.Plus.singleFunctors B).shiftIso n 0 n (add_zero n)).inv.app X
  simp only [shiftedStalkValueIso, dite_eq_right hn, id, Iso.trans_inv, NatTrans.comp_app,
    isoWhiskerLeft_inv, whiskerLeft_app, isoWhiskerRight_inv, whiskerRight_app, Iso.symm_inv]
  change (H.map (R.map e) ≫ H.map ((R.commShiftIso n).hom.app Y)) ≫
    (H.isoShift n).hom.app (R.obj Y) = _
  rw [← H.map_comp]
  change H.map (ShiftedHom.map e R) ≫ (H.isoShift n).hom.app (R.obj Y) = _
  have hz := plus_homology_isoShiftZero (R.obj Y⟦n⟧)
  have hzInv : (H.isoShiftZero ℤ).inv.app (R.obj Y⟦n⟧) = 𝟙 _ := by
    have he := (H.isoShiftZero ℤ).inv_hom_id_app (R.obj Y⟦n⟧)
    change _ ≫ (H.isoShiftZero ℤ).hom.app (R.obj Y⟦n⟧) = _ at he
    rw [hz, Category.comp_id] at he
    exact he
  simp only [Functor.isoShift, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, Iso.symm_hom, hzInv, Functor.shiftMap]
  erw [Category.id_comp]
  rfl

private lemma exactHomologyIso_stalk (n : ℤ) (X : B) :
    (exactHomologyIso U n).hom.app ((DerivedCategory.Plus.singleFunctor B n).obj X) ≫
      U.map ((singlePlusHomologyIso (B := B) n).hom.app X) =
    (rightDerivedStalkHomologyIso U n).hom.app X := by
  by_cases hn : n = 0
  · subst n
    simpa [rightDerivedStalkHomologyIso, shiftedStalkValueIso] using exactHomologyIso_stalk_zero U X
  have h := exactHomologyShiftMapQ U (stalkShiftedMap n X) 0 n (add_zero n)
  have hs := singlePlusHomologyShiftMap n X
  have hu := exactHomologyIso_stalk_zero U X
  have h' : (shiftedStalkValueIso U n).inv.app X ≫
      (exactHomologyIso U n).hom.app ((DerivedCategory.Plus.singleFunctor B n).obj X) =
    (exactHomologyIso U 0).hom.app ((DerivedCategory.Plus.singleFunctor B 0).obj X) ≫
      U.map ((DerivedCategory.Plus.homologyFunctor B 0).shiftMap
        ((stalkShiftedMap n X).map DerivedCategory.Plus.Q) 0 n (add_zero n)) := by
    rw [shiftedStalkValueIso_inv_shiftMap U n hn X]
    rw [stalkShiftedMap_Q n X] at h ⊢
    exact h
  apply (cancel_epi ((shiftedStalkValueIso U n).inv.app X)).1
  simp only [rightDerivedStalkHomologyIso, Iso.trans_hom, NatTrans.comp_app, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% h', ← U.map_comp, hs, hu]

/-- For an exact coefficient functor the derived column edge is the
canonical identification of homology after applying the functor. -/
lemma derivedColumn_exact (n : ℤ) :
    derivedTruncationEdge U n = (exactHomologyIso U n).hom := by
  have h := derivedColumn_comparison U U n (𝟙 U) (exactHomologyIso U n).hom (fun X => by
    rw [exactHomologyIso_stalk U n X, NatTrans.id_app, Category.comp_id])
  simpa only [whiskerLeft_id', Category.comp_id] using h


end ExactFunctor

end ColumnEdge

section ExactPostcomposition

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (U : B ⥤ C) [F.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

/-- After exact postcomposition, read the cohomology of the actual
right-derived composition by its comparison with the right-derived
original functor. -/
def exactPostcompositionMap (n : ℕ) : rightValue (F ⋙ U) n ⟶ rightValue F n ⋙ U :=
  whiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
    (whiskerRight (comparisonValue F U) (DerivedCategory.Plus.homologyFunctor C (n : ℤ)) ≫
      whiskerLeft F.rightDerivedFunctorPlus (exactHomologyIso U (n : ℤ)).hom)

lemma exactPostcompositionMap_connectors {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    rightBoundary (F ⋙ U) hS n ≫ (exactPostcompositionMap F U (n+1)).app S.X₁ =
    (exactPostcompositionMap F U n).app S.X₃ ≫ U.map (rightBoundary F hS n) := by
  let HC := DerivedCategory.Plus.homologyFunctor C 0
  let HB := DerivedCategory.Plus.homologyFunctor B 0
  let η := comparisonValue F U
  let T := plusTriangle A hS
  let f : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ) := T.mor₃
  have h := ShiftedHom.map_naturality f η
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  rw [ShiftedHom.comp_map] at h
  have hn : (1 : ℤ) + (n : ℤ) = ((n+1 : ℕ) : ℤ) := by omega
  have hh := congrArg (fun t => HC.shiftMap t (n : ℤ) ((n+1 : ℕ) : ℤ) hn) h
  rw [HC.shiftMap_comp, HC.shiftMap_comp'] at hh
  change HC.shiftMap (f.map (F ⋙ U).rightDerivedFunctorPlus) (n : ℤ) ((n+1 : ℕ) : ℤ) hn ≫
      (HC.shift ((n+1 : ℕ) : ℤ)).map (η.app T.obj₁) ≫
      (exactHomologyIso U ((n+1 : ℕ) : ℤ)).hom.app (F.rightDerivedFunctorPlus.obj T.obj₁) =
    ((HC.shift (n : ℤ)).map (η.app T.obj₃) ≫
      (exactHomologyIso U (n : ℤ)).hom.app (F.rightDerivedFunctorPlus.obj T.obj₃)) ≫
      U.map (HB.shiftMap (f.map F.rightDerivedFunctorPlus) (n : ℤ) ((n+1 : ℕ) : ℤ) hn)
  simp only [Category.assoc]
  rw [reassoc_of% hh, exactHomologyIso_shiftMap]

end ExactPostcomposition

section NaturalTransformations

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
  (F U : A ⥤ B) [F.Additive] [U.Additive]

/-- The component map of right-derived values of a transformation of coefficient functors. -/
def derivedValueTransformation (τ : F ⟶ U) (n : ℕ) :
    rightValue F n ⟶ rightValue U n :=
  whiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
    (whiskerRight τ.rightDerivedFunctorPlus (DerivedCategory.Plus.homologyFunctor B (n : ℤ)))

lemma rightBoundary_derivedValueTransformation (τ : F ⟶ U)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    rightBoundary F hS n ≫ (derivedValueTransformation F U τ (n+1)).app S.X₁ =
      (derivedValueTransformation F U τ n).app S.X₃ ≫ rightBoundary U hS n := by
  let T := plusTriangle A hS
  let η := τ.rightDerivedFunctorPlus
  let f : F.rightDerivedFunctorPlus.mapTriangle.obj T ⟶
      U.rightDerivedFunctorPlus.mapTriangle.obj T :=
    { hom₁ := η.app T.obj₁
      hom₂ := η.app T.obj₂
      hom₃ := η.app T.obj₃
      comm₁ := η.naturality T.mor₁
      comm₂ := η.naturality T.mor₂
      comm₃ := by
        dsimp only [Functor.mapTriangle_obj, Pretriangulated.Triangle.mk_mor₃]
        rw [Category.assoc, NatTrans.shift_app_comm η (1 : ℤ), ← Category.assoc,
          η.naturality T.mor₃, Category.assoc] }
  exact ((DerivedCategory.Plus.homologyFunctor B 0).homologySequenceδ_naturality
    f (n : ℤ) ((n+1 : ℕ) : ℤ) (by omega)).symm

/-- Transport the right-derived values along a natural isomorphism. -/
def derivedValueIso {F U : A ⥤ B} [F.Additive] [U.Additive] (a : F ≅ U) (n : ℕ) : rightValue F n ≅ rightValue U n := by
  let e : F.rightDerivedFunctorPlus ≅ U.rightDerivedFunctorPlus :=
    { hom := a.hom.rightDerivedFunctorPlus
      inv := a.inv.rightDerivedFunctorPlus
      hom_inv_id := by
        rw [← NatTrans.rightDerivedFunctorPlus_comp, a.hom_inv_id, NatTrans.rightDerivedFunctorPlus_id]
      inv_hom_id := by
        rw [← NatTrans.rightDerivedFunctorPlus_comp, a.inv_hom_id, NatTrans.rightDerivedFunctorPlus_id] }
  exact isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
    (isoWhiskerRight e (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)))

end NaturalTransformations


section ColumnFactor

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (V U : B ⥤ C) [F.Additive] [V.Additive] [U.Additive]
  [PreservesFiniteLimits V] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

lemma derivedSecondEdge_through_exactPostcomposition (η : V ⟶ U) (n : ℕ)
    (hcol : derivedTruncationEdge V (n : ℤ) ≫
      whiskerLeft (DerivedCategory.Plus.homologyFunctor B (n : ℤ)) η =
      whiskerRight η.rightDerivedFunctorPlus (DerivedCategory.Plus.homologyFunctor C (n : ℤ)) ≫
        derivedTruncationEdge U (n : ℤ))
    (hexact : derivedTruncationEdge U (n : ℤ) = (exactHomologyIso U (n : ℤ)).hom) :
    derivedSecondEdge V F n ≫ whiskerLeft (rightValue F n) η =
      derivedValueTransformation (F ⋙ V) (F ⋙ U) (whiskerLeft F η) n ≫
        exactPostcompositionMap F U n := by
  apply NatTrans.ext
  funext X
  let T := (DerivedCategory.Plus.singleFunctor A 0).obj X
  let H := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  let Y := F.rightDerivedFunctorPlus.obj T
  change (H.map ((comparisonValue F V).app T) ≫ (derivedTruncationEdge V (n : ℤ)).app Y) ≫
      η.app ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj Y) =
    H.map ((whiskerLeft F η).rightDerivedFunctorPlus.app T) ≫
      H.map ((comparisonValue F U).app T) ≫ (exactHomologyIso U (n : ℤ)).hom.app Y
  have hc := congrArg (fun t => t.app Y) hcol
  change (derivedTruncationEdge V (n : ℤ)).app Y ≫
      η.app ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj Y) =
    H.map (η.rightDerivedFunctorPlus.app Y) ≫ (derivedTruncationEdge U (n : ℤ)).app Y at hc
  have hcomp := congrArg (fun t => t.app T) (comparisonValue_natural_right F V U η)
  change (comparisonValue F V).app T ≫ η.rightDerivedFunctorPlus.app Y =
    (whiskerLeft F η).rightDerivedFunctorPlus.app T ≫ (comparisonValue F U).app T at hcomp
  rw [Category.assoc, hc, hexact, ← H.map_comp_assoc, hcomp, H.map_comp_assoc]

end ColumnFactor


section ColumnConnectors

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (V U : B ⥤ C) [F.Additive] [V.Additive] [U.Additive]
  [PreservesFiniteLimits V] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

private lemma derivedColumn_inclusion_connectors (η : V ⟶ U)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    rightBoundary (F ⋙ V) hS n ≫
        (derivedSecondEdge V F (n+1) ≫ whiskerLeft (rightValue F (n+1)) η).app S.X₁ =
      (derivedSecondEdge V F n ≫ whiskerLeft (rightValue F n) η).app S.X₃ ≫
        U.map (rightBoundary F hS n) := by
  let τ := whiskerLeft F η
  rw [derivedSecondEdge_through_exactPostcomposition F V U η (n+1)
      (derivedColumn_natural V U η _) (derivedColumn_exact U _),
    derivedSecondEdge_through_exactPostcomposition F V U η n
      (derivedColumn_natural V U η _) (derivedColumn_exact U _)]
  simp only [NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% (rightBoundary_derivedValueTransformation (F ⋙ V) (F ⋙ U) τ hS n),
    exactPostcompositionMap_connectors]

end ColumnConnectors

section RestrictionIdentification

private abbrev groupRestrictionInclusion :
    quotientInvariants.{u,v,w} k G N ⟶ forgetQuotient.{u,v,w} k G N where
  app M := ModuleCat.ofHom (Representation.invariants M.ρ).subtype
  naturality _ _ f := by ext x; rfl

private def derivedRestrictionUnderlying (n : ℕ) :
    rightValue (totalInvariants.{u,v,w} k G N) n ⟶
      rightValue (subgroupInvariants.{u,v,w} k G N) n ⋙ forgetQuotient.{u,v,w} k G N :=
  derivedSecondEdge (quotientInvariants.{u,v,w} k G N) (subgroupInvariants.{u,v,w} k G N) n ≫
    whiskerLeft _ (groupRestrictionInclusion.{u,v,w} k G N)

/-- Compare the underlying restriction with the canonical derived restriction
using effacement on the category of G-representations. -/
private lemma restriction_from_normalization (C : CohomologyModels.{u,v,w} k G N)
    (hδ : ∀ {S : ShortComplex (Rep.{max u v w} k G)} (hS : S.ShortExact) (n : ℕ),
      rightBoundary (totalInvariants.{u,v,w} k G N) hS n ≫
        (derivedRestrictionUnderlying.{u,v,w} k G N (n+1)).app S.X₁ =
      (derivedRestrictionUnderlying.{u,v,w} k G N n).app S.X₃ ≫
        (forgetQuotient.{u,v,w} k G N).map (rightBoundary (subgroupInvariants.{u,v,w} k G N) hS n))
    (h₀ : ∀ (M : Rep.{max u v w} k G)
      (x : (totalInvariants.{u,v,w} k G N).obj M),
      ((derivedRestrictionUnderlying.{u,v,w} k G N 0).app M).hom
          (((degreeZeroUnit (totalInvariants.{u,v,w} k G N)).app M).hom x) =
      (((degreeZeroUnit (subgroupInvariants.{u,v,w} k G N)).app M).hom x.val)) :
    ∀ n, derivedRestrictionUnderlying.{u,v,w} k G N n ≫
        (isoWhiskerRight (C.subgroupDerived n) _ ≪≫ C.underlying n).hom =
      (C.totalDerived n).hom ≫
        whiskerRight (restrictionCochain.{u,v,w} k G N) (HomologicalComplex.homologyFunctor _ (.up ℕ) n) := by
  let F := subgroupInvariants.{u,v,w} k G N
  let U := forgetQuotient.{u,v,w} k G N
  let W := totalInvariants.{u,v,w} k G N
  let L := restriction.{u,v,w} k G N
  let S := rightSystem W
  let T := postcomposeCohomological U (rightSystem F)
  let D := normSystem.{u,v,w} k N L
  let B := normSystem.{u,v,w} k G (𝟭 _)
  let e n := isoWhiskerRight (C.subgroupDerived n) U ≪≫ C.underlying n
  have hS : IsCohomological S := UniversalDeltaFunctors.rightDelta _ _ W
  have hD : IsCohomological D := normSystem_cohomological k N L
  have hvanish (I : Rep.{max u v w} k G) [Injective I] (n : ℕ) : IsZero ((S.value (n+1)).obj I) :=
    ClassicalDerivedValues.rightInjectiveVanishing _ _ W I n
  have hU := UniversalDeltaFunctors.universal_of_injective_vanishing S hS @hvanish
  let d : CohomologicalMorphism S T := ⟨derivedRestrictionUnderlying.{u,v,w} k G N, hδ⟩
  have he : ∀ {S' : ShortComplex (Rep.{max u v w} k G)} (hS' : S'.ShortExact) n,
      T.δ hS' n ≫ (e (n+1)).hom.app S'.X₁ = (e n).hom.app S'.X₃ ≫ D.δ hS' n := by
    obtain ⟨_, h⟩ := C.subgroup_connectors
    exact h
  let m : CohomologicalMorphism T D := ⟨fun n => (e n).hom, he⟩
  have ht : ∀ {S' : ShortComplex (Rep.{max u v w} k G)} (hS' : S'.ShortExact) n,
      S.δ hS' n ≫ (C.totalDerived (n+1)).hom.app S'.X₁ =
        (C.totalDerived n).hom.app S'.X₃ ≫ B.δ hS' n := by
    obtain ⟨_, h⟩ := C.total_connectors
    exact h
  let b : CohomologicalMorphism S B := ⟨fun n => (C.totalDerived n).hom, ht⟩
  let r : CohomologicalMorphism B D :=
    { component n := whiskerRight (restrictionCochain.{u,v,w} k G N)
        (HomologicalComplex.homologyFunctor _ (.up ℕ) n)
      comm hS n := cochainTransformation_connectors (restrictionCochain.{u,v,w} k G N)
        (normExact k G hS) (normExact_comp k N L hS) n }
  let left := GroupLowDegreesAndCoefficients.deltaComposition d m
  let right := GroupLowDegreesAndCoefficients.deltaComposition b r
  have hzero : left.component 0 = right.component 0 := by
    apply NatTrans.ext
    funext M
    apply (cancel_epi ((degreeZeroIso W).hom.app M)).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨z, hz, hz₀⟩ := C.total_augmentation M x
    obtain ⟨y, hy, hy₀⟩ := C.subgroup_augmentation M x.val
    change ((e 0).hom.app M).hom (((derivedRestrictionUnderlying.{u,v,w} k G N 0).app M).hom
          (((degreeZeroUnit W).app M).hom x)) =
      (HomologicalComplex.homologyMap ((restrictionCochain.{u,v,w} k G N).app M) 0).hom
        (((C.totalDerived 0).hom.app M).hom (((degreeZeroUnit W).app M).hom x))
    rw [h₀ M x]
    change ((e 0).hom.app M).hom
        (((whiskerRight (degreeZeroUnit F) U).app M).hom x.val) = _
    erw [hy₀, hz₀]
    let R := (restrictionCochain.{u,v,w} k G N).app M
    let K := (repHomogeneousFunctor.{u,v,w} k G).obj M
    let J := (repHomogeneousFunctor.{u,v,w} k N).obj (L.obj M)
    have hπ := congrArg (fun f => f.hom z) (HomologicalComplex.homologyπ_naturality R 0)
    change _ =
      (HomologicalComplex.homologyMap R 0).hom ((K.homologyπ 0).hom z)
    change (HomologicalComplex.homologyMap R 0).hom ((K.homologyπ 0).hom z) =
      (J.homologyπ 0).hom ((HomologicalComplex.cyclesMap R 0).hom z) at hπ
    rw [hπ]
    congr 1
    apply (ModuleCat.mono_iff_injective (J.iCycles 0)).mp inferInstance
    have hi := congrArg (fun f => f.hom z) (HomologicalComplex.cyclesMap_i R 0)
    change (J.iCycles 0).hom ((HomologicalComplex.cyclesMap R 0).hom z) =
      (R.f 0).hom ((K.iCycles 0).hom z) at hi
    change (J.iCycles 0).hom y = (J.iCycles 0).hom ((HomologicalComplex.cyclesMap R 0).hom z)
    rw [hi]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change ((J.iCycles 0).hom y).hom (GroupBar.Large.single.{u,v,w} k N c 1) =
      ((R.f 0).hom ((K.iCycles 0).hom z)).hom (GroupBar.Large.single.{u,v,w} k N c 1)
    have hr := restrictionCochain_formula.{u,v,w} k G N M 0 ((K.iCycles 0).hom z) c
    erw [hy, hr, hz]
  obtain ⟨w, _, hw⟩ := hU D hD (right.component 0)
  have h := (hw left hzero).trans (hw right rfl).symm
  intro n
  exact congrArg (fun a : CohomologicalMorphism S D => a.component n) h

end RestrictionIdentification

section EdgeAssembly
variable {k G N}

/-- Obtain the ordinary restriction with values in fixed vectors. Its
underlying map is the pullback on homogeneous cochains. -/
private def restrictionFromDerived (C : CohomologyModels.{u,v,w} k G N)
    (h : ∀ n, derivedRestrictionUnderlying.{u,v,w} k G N n ≫
        (isoWhiskerRight (C.subgroupDerived n) _ ≪≫ C.underlying n).hom =
      (C.totalDerived n).hom ≫
        whiskerRight (restrictionCochain.{u,v,w} k G N) (HomologicalComplex.homologyFunctor _ (.up ℕ) n)) :
    RestrictionEdge C where
  cochain := restrictionCochain.{u,v,w} k G N
  formula := restrictionCochain_formula.{u,v,w} k G N
  map n :=
    (C.totalDerived n).inv ≫ derivedSecondEdge (quotientInvariants.{u,v,w} k G N)
      (subgroupInvariants.{u,v,w} k G N) n ≫
    (isoWhiskerRight (C.subgroupDerived n) (quotientInvariants.{u,v,w} k G N)).hom
  ordinary n M x := by
    let V := quotientInvariants.{u,v,w} k G N
    let U := forgetQuotient.{u,v,w} k G N
    let i := groupRestrictionInclusion.{u,v,w} k G N
    let F := subgroupInvariants.{u,v,w} k G N
    let e := (C.totalDerived n).app M
    let f := (derivedSecondEdge V F n).app M
    let s := (C.subgroupDerived n).hom.app M
    let c := (C.underlying n).hom.app M
    let r : (repHomogeneousCohomology.{u,v,w} k G n).obj M ⟶
        (restriction.{u,v,w} k G N ⋙ repHomogeneousCohomology.{u,v,w} k N n).obj M :=
      HomologicalComplex.homologyMap ((restrictionCochain.{u,v,w} k G N).app M) n
    have hn : V.map s ≫ i.app ((C.subgroup n).obj M) = i.app ((rightValue F n).obj M) ≫ U.map s :=
      i.naturality s
    have hr : f ≫ i.app ((rightValue F n).obj M) ≫ U.map s ≫ c = e.hom ≫ r := by
      have hr := congrArg (fun t => t.app M) (h n)
      simp only [derivedRestrictionUnderlying, NatTrans.comp_app, Iso.trans_hom,
        isoWhiskerRight_hom, whiskerRight_app, whiskerLeft_app, Category.assoc] at hr
      exact hr
    have hh : e.inv ≫ f ≫ V.map s ≫ i.app ((C.subgroup n).obj M) ≫ c = r := by
      rw [reassoc_of% hn]
      exact (congrArg (e.inv ≫ ·) hr).trans (e.inv_hom_id_assoc r)
    exact congrArg (fun t => t.hom x) hh

private lemma restrictionFromDerived_eq (C : CohomologyModels.{u,v,w} k G N)
    {P : Package (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N)}
    (E : ObjectEdges (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) P)
    (h : ∀ n, derivedRestrictionUnderlying.{u,v,w} k G N n ≫
        (isoWhiskerRight (C.subgroupDerived n) _ ≪≫ C.underlying n).hom =
      (C.totalDerived n).hom ≫
        whiskerRight (restrictionCochain.{u,v,w} k G N) (HomologicalComplex.homologyFunctor _ (.up ℕ) n))
    (n : ℕ) :
    (C.totalDerived n).hom ≫ (restrictionFromDerived C h).map n =
      classicalColumn (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N)
        (E.truncation n) E.degreeZero ≫
      (isoWhiskerRight (C.subgroupDerived n) (quotientInvariants.{u,v,w} k G N)).hom := by
  rw [classicalColumn_eq_derivedSecondEdge]
  exact Iso.hom_inv_id_assoc _ _

private lemma restrictionUnderlying_connectors
    {S : ShortComplex (Rep.{max u v w} k G)} (hS : S.ShortExact) (n : ℕ) :
    rightBoundary (totalInvariants.{u,v,w} k G N) hS n ≫
      (derivedRestrictionUnderlying.{u,v,w} k G N (n+1)).app S.X₁ =
    (derivedRestrictionUnderlying.{u,v,w} k G N n).app S.X₃ ≫
      (forgetQuotient.{u,v,w} k G N).map (rightBoundary (subgroupInvariants.{u,v,w} k G N) hS n) :=
  derivedColumn_inclusion_connectors (subgroupInvariants.{u,v,w} k G N)
    (quotientInvariants.{u,v,w} k G N) (forgetQuotient.{u,v,w} k G N)
    (groupRestrictionInclusion.{u,v,w} k G N) hS n

private lemma restrictionUnderlying_degreeZero (M : Rep.{max u v w} k G)
    (x : (totalInvariants.{u,v,w} k G N).obj M) :
    ((derivedRestrictionUnderlying.{u,v,w} k G N 0).app M).hom
        (((degreeZeroUnit (totalInvariants.{u,v,w} k G N)).app M).hom x) =
      (((degreeZeroUnit (subgroupInvariants.{u,v,w} k G N)).app M).hom x.val) := by
  let F := subgroupInvariants.{u,v,w} k G N
  let V := quotientInvariants.{u,v,w} k G N
  let U := forgetQuotient.{u,v,w} k G N
  let i := groupRestrictionInclusion.{u,v,w} k G N
  have ht := i.naturality ((degreeZeroUnit F).app M)
  have h : (degreeZeroUnit (F ⋙ V)).app M ≫ (derivedRestrictionUnderlying.{u,v,w} k G N 0).app M =
      i.app (F.obj M) ≫ U.map ((degreeZeroUnit F).app M) := by
    change (degreeZeroUnit (F ⋙ V)).app M ≫
      (derivedSecondEdge V F 0).app M ≫ i.app ((rightValue F 0).obj M) = _
    rw [reassoc_of% (derivedSecondEdge_degreeZeroUnit F V M)]
    exact ht
  exact congrArg (fun t => t.hom x) h

set_option maxHeartbeats 4000000 in
private def ordinaryRestriction (C : CohomologyModels.{u,v,w} k G N) : RestrictionEdge C := by
  have hs := @restriction_from_normalization.{u,v,w} k G _ _ N _ C
  apply restrictionFromDerived C
  apply hs
  · intro S hS n
    exact @restrictionUnderlying_connectors.{u,v,w} k G _ _ N _ S hS n
  · intro M x
    exact @restrictionUnderlying_degreeZero.{u,v,w} k G _ _ N _ M x

private lemma ordinaryRestriction_eq (C : CohomologyModels.{u,v,w} k G N)
    {P : Package (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N)}
    (E : ObjectEdges (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N) P)
    (n : ℕ) :
    (C.totalDerived n).hom ≫ (ordinaryRestriction C).map n =
      classicalColumn (subgroupInvariants.{u,v,w} k G N) (quotientInvariants.{u,v,w} k G N)
        (E.truncation n) E.degreeZero ≫
      (isoWhiskerRight (C.subgroupDerived n) (quotientInvariants.{u,v,w} k G N)).hom := by
  unfold ordinaryRestriction
  apply restrictionFromDerived_eq

end EdgeAssembly

section ExactPrecompositionProof

open CategoryTheory.Pretriangulated CategoryTheory.Localization

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 240000

section ExactStalkTriangle

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (I : A ⥤ B) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  {S : ShortComplex A} (hS : S.ShortExact)

/-- The triangulated functor of an exact functor carries the stalk triangle
of a short exact sequence to the stalk triangle of its image. -/
def exactMapStalkTriangleIso :
    I.mapDerivedCategory.mapTriangle.obj hS.singleTriangle ≅
      (hS.map_of_exact I).singleTriangle :=
  Triangle.isoMk _ _
    ((I.mapDerivedCategorySingleFunctor 0).app S.X₁)
    ((I.mapDerivedCategorySingleFunctor 0).app S.X₂)
    ((I.mapDerivedCategorySingleFunctor 0).app S.X₃)
    ((I.mapDerivedCategorySingleFunctor 0).hom.naturality S.f)
    ((I.mapDerivedCategorySingleFunctor 0).hom.naturality S.g)
    (by
      change ShiftedHom.map hS.singleδ I.mapDerivedCategory ≫
          ((I.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦(1 : ℤ)⟧' =
        (I.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫ (hS.map_of_exact I).singleδ
      rw [hS.mapShiftedHom_singleδ I, Category.assoc, Category.assoc, ← Functor.map_comp,
        Iso.inv_hom_id_app]
      erw [(shiftFunctor (DerivedCategory B) (1 : ℤ)).map_id, Category.comp_id])

/-- The bounded-below stalk triangle is the original stalk triangle under
the inclusion into the unbounded derived category. -/
def plusStalkTriangleInclusionIso :
    (DerivedCategory.Plus.ι (C := A)).mapTriangle.obj (plusTriangle A hS) ≅ hS.singleTriangle :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [plusTriangle, ShortComplex.ShortExact.singleTriangle]; rfl)
    (by simp [plusTriangle, ShortComplex.ShortExact.singleTriangle]; rfl)
    (by
      dsimp [Functor.mapTriangle, plusTriangle, ShortComplex.ShortExact.singleTriangle]
      simp only [Category.assoc,
        (shiftFunctor (DerivedCategory A) (1 : ℤ)).map_id, Category.comp_id, Category.id_comp]
      erw [Iso.inv_hom_id_app, Category.comp_id])


end ExactStalkTriangle
section BoundaryNaturality

variable {A B : Type*} [Category A] [Category B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- A shift-compatible transformation of triangulated functors acts
functorially on each distinguished triangle. -/
def mapTriangleTransformation {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {L R : C ⥤ D} [L.CommShift ℤ] [R.CommShift ℤ]
    (τ : L ⟶ R) [τ.CommShift ℤ] (T : Triangle C) :
    L.mapTriangle.obj T ⟶ R.mapTriangle.obj T where
  hom₁ := τ.app T.obj₁
  hom₂ := τ.app T.obj₂
  hom₃ := τ.app T.obj₃
  comm₁ := τ.naturality T.mor₁
  comm₂ := τ.naturality T.mor₂
  comm₃ := by
    dsimp [Functor.mapTriangle]
    simp only [Category.assoc,
      NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁, NatTrans.naturality_assoc]

end BoundaryNaturality
section ExactDerivedPrecomposition

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  (I : A ⥤ B) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]

/-- The exact functor on derived categories restricts to the bounded-below parts. -/
def exactDerivedPlus : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B :=
  ObjectProperty.lift _ (DerivedCategory.Plus.ι ⋙ I.mapDerivedCategory) (by
    intro X
    obtain ⟨n, K, e, hK⟩ := X.property
    let := hK
    exact ⟨n, (I.mapHomologicalComplex (.up ℤ)).obj K,
      I.mapDerivedCategory.mapIso e ≪≫ I.mapDerivedCategoryFactors.app K, inferInstance⟩)

instance : (exactDerivedPlus I).CommShift ℤ := ObjectProperty.commShiftLift ..

def exactDerivedPlusCompι :
    exactDerivedPlus I ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ I.mapDerivedCategory :=
  ObjectProperty.liftCompιIso ..

instance : (exactDerivedPlusCompι I).hom.CommShift ℤ := ObjectProperty.commShift_liftCompιIso_hom ..

private def exactDerivedPlusFactorsι :
    (DerivedCategory.Plus.Q ⋙ exactDerivedPlus I) ⋙ DerivedCategory.Plus.ι ≅
      (I.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ DerivedCategory.Plus.ι :=
  (associator _ _ _) ≪≫ isoWhiskerLeft _ (exactDerivedPlusCompι I) ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (DerivedCategory.Plus.QCompιIso A) _ ≪≫
    (associator _ _ _) ≪≫ isoWhiskerLeft _ I.mapDerivedCategoryFactors ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight I.mapCochainComplexPlusCompι.symm _ ≪≫
    (associator _ _ _) ≪≫
    isoWhiskerLeft _ (DerivedCategory.Plus.QCompιIso B).symm ≪≫
    (associator _ _ _).symm

def exactDerivedPlusFactors :
    DerivedCategory.Plus.Q ⋙ exactDerivedPlus I ≅
      I.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  ((FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := B))).whiskeringRight _).preimageIso
    (exactDerivedPlusFactorsι I)

instance : (exactDerivedPlusFactors I).hom.CommShift ℤ := by
  refine NatTrans.CommShift.of_comp_faithful (DerivedCategory.Plus.ι (C := B)) ?_
  have h := ((FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι (C := B))).whiskeringRight _).map_preimage (exactDerivedPlusFactorsι I).hom
  change whiskerRight (exactDerivedPlusFactors I).hom (DerivedCategory.Plus.ι (C := B)) =
    (exactDerivedPlusFactorsι I).hom at h
  rw [h]
  unfold exactDerivedPlusFactorsι
  simp only [Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
  refine @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · repeat' refine @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ ?_ ?_
    all_goals infer_instance

variable (J : B ⥤ D) [J.Additive]

private def cochainPlusCompIsoι :
    (I.mapCochainComplexPlus ⋙ J.mapCochainComplexPlus) ⋙ CochainComplex.Plus.ι D ≅
      (I ⋙ J).mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D :=
  (associator _ _ _) ≪≫ isoWhiskerLeft _ J.mapCochainComplexPlusCompι ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight I.mapCochainComplexPlusCompι _ ≪≫
    (associator _ _ _) ≪≫
    isoWhiskerLeft _ (Functor.mapHomologicalComplexCompIso (Iso.refl (I ⋙ J)) (.up ℤ)) ≪≫
    (I ⋙ J).mapCochainComplexPlusCompι.symm

private def cochainPlusCompIso :
    I.mapCochainComplexPlus ⋙ J.mapCochainComplexPlus ≅ (I ⋙ J).mapCochainComplexPlus :=
  ((FullyFaithful.ofFullyFaithful (CochainComplex.Plus.ι D)).whiskeringRight _).preimageIso
    (cochainPlusCompIsoι I J)

private instance : (cochainPlusCompIso I J).hom.CommShift ℤ := by
  refine NatTrans.CommShift.of_comp_faithful (CochainComplex.Plus.ι D) ?_
  have h := ((FullyFaithful.ofFullyFaithful (CochainComplex.Plus.ι D)).whiskeringRight _).map_preimage
    (cochainPlusCompIsoι I J).hom
  change whiskerRight (cochainPlusCompIso I J).hom (CochainComplex.Plus.ι D) =
    (cochainPlusCompIsoι I J).hom at h
  rw [h]
  unfold cochainPlusCompIsoι
  simp only [Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
  refine @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · repeat' refine @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ ?_ ?_
    all_goals infer_instance

variable [EnoughInjectives A] [EnoughInjectives B]

/-- The canonical comparison with the exact functor in the first slot.
No acyclicity of the exact functor's image is required for this map. -/
def derivedPrecomposition :
    (I ⋙ J).rightDerivedFunctorPlus ⟶ exactDerivedPlus I ⋙ J.rightDerivedFunctorPlus :=
  Functor.natTransOfIsRightDerivedFunctorComp (cochainPlusCompIso I J)
    DerivedCategory.Plus.Q DerivedCategory.Plus.Q DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso A) (exactDerivedPlusFactors I).inv
    J.rightDerivedFunctorPlusUnit (I ⋙ J).rightDerivedFunctorPlusUnit

@[reassoc]
lemma derivedPrecomposition_unit (K : CochainComplex.Plus A) :
    (I ⋙ J).rightDerivedFunctorPlusUnit.app K ≫
      (derivedPrecomposition I J).app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map ((cochainPlusCompIso I J).inv.app K) ≫
      J.rightDerivedFunctorPlusUnit.app (I.mapCochainComplexPlus.obj K) ≫
      J.rightDerivedFunctorPlus.map ((exactDerivedPlusFactors I).inv.app K) :=
  Functor.comp_natTransOfIsRightDerivedFunctorComp_app (cochainPlusCompIso I J)
    DerivedCategory.Plus.Q DerivedCategory.Plus.Q DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso A) (exactDerivedPlusFactors I).inv
    J.rightDerivedFunctorPlusUnit (I ⋙ J).rightDerivedFunctorPlusUnit K

instance : (derivedPrecomposition I J).CommShift ℤ := by
  unfold derivedPrecomposition
  infer_instance


instance : (exactDerivedPlus I).Additive := by
  have : (exactDerivedPlus I ⋙ DerivedCategory.Plus.ι).Additive :=
    Functor.additive_of_iso (exactDerivedPlusCompι I).symm
  exact Functor.additive_of_comp_faithful _ DerivedCategory.Plus.ι

private def exactDerivedPlusStalkIsoι :
    (DerivedCategory.Plus.singleFunctor A 0 ⋙ exactDerivedPlus I) ⋙ DerivedCategory.Plus.ι ≅
      (I ⋙ DerivedCategory.Plus.singleFunctor B 0) ⋙ DerivedCategory.Plus.ι :=
  (associator _ _ _) ≪≫ isoWhiskerLeft _ (exactDerivedPlusCompι I) ≪≫
    (associator _ _ _).symm ≪≫ (I.mapDerivedCategorySingleFunctor 0) ≪≫
    (associator _ _ _).symm

/-- The bounded-below exact image of a stalk is the stalk of its image. -/
def exactDerivedPlusStalkIso :
    DerivedCategory.Plus.singleFunctor A 0 ⋙ exactDerivedPlus I ≅
      I ⋙ DerivedCategory.Plus.singleFunctor B 0 :=
  ((FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := B))).whiskeringRight _).preimageIso
    (exactDerivedPlusStalkIsoι I)

omit [EnoughInjectives A] [EnoughInjectives B] in
private lemma exactDerivedPlusStalkIso_hom_map (X : A) :
    (DerivedCategory.Plus.ι (C := B)).map ((exactDerivedPlusStalkIso I).hom.app X) =
      (I.mapDerivedCategorySingleFunctor 0).hom.app X := by
  have h := ((FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := B))).whiskeringRight _).map_preimage
    (exactDerivedPlusStalkIsoι I).hom
  have hh := NatTrans.congr_app h X
  change (DerivedCategory.Plus.ι (C := B)).map ((exactDerivedPlusStalkIso I).hom.app X) =
    (exactDerivedPlusStalkIsoι I).hom.app X at hh
  rw [hh]
  simp [exactDerivedPlusStalkIsoι, exactDerivedPlusCompι, ObjectProperty.liftCompιIso]
  erw [Category.id_comp]

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I] [EnoughInjectives A] [EnoughInjectives B] in
/-- The termwise composition comparison is the identity on every bounded
cochain complex. -/
lemma cochainPlusCompIso_inv_app (K : CochainComplex.Plus A) :
    (cochainPlusCompIso I J).inv.app K = 𝟙 _ := by
  apply (CochainComplex.Plus.ι D).map_injective
  change _ = 𝟙 _
  have h := ((FullyFaithful.ofFullyFaithful (CochainComplex.Plus.ι D)).whiskeringRight _).map_preimage
    (cochainPlusCompIsoι I J).inv
  have hh := NatTrans.congr_app h K
  change (CochainComplex.Plus.ι D).map ((cochainPlusCompIso I J).inv.app K) =
    (cochainPlusCompIsoι I J).inv.app K at hh
  rw [hh]
  ext n
  simp [cochainPlusCompIsoι, Functor.mapHomologicalComplexCompIso, Functor.mapCochainComplexPlusCompι]

omit [EnoughInjectives A] [EnoughInjectives B] in
private lemma exactDerivedPlusFactors_hom_app_map (K : CochainComplex.Plus A) :
    (DerivedCategory.Plus.ι (C := B)).map ((exactDerivedPlusFactors I).hom.app K) =
      I.mapDerivedCategoryFactors.hom.app K.obj := by
  have h := ((FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := B))).whiskeringRight _).map_preimage
    (exactDerivedPlusFactorsι I).hom
  have hh := NatTrans.congr_app h K
  change (DerivedCategory.Plus.ι (C := B)).map ((exactDerivedPlusFactors I).hom.app K) =
    (exactDerivedPlusFactorsι I).hom.app K at hh
  rw [hh]
  simp [exactDerivedPlusFactorsι, exactDerivedPlusCompι, ObjectProperty.liftCompιIso, Functor.mapCochainComplexPlusCompι]
  erw [I.mapDerivedCategory.map_id, Category.id_comp]
  exact Category.id_comp _

omit [EnoughInjectives A] [EnoughInjectives B] in
/-- On a stalk, the canonical exact derived comparison is induced by the
termwise exact complex functor followed by the literal stalk comparison. -/
lemma exactDerivedPlusStalkIso_app (X : A) :
    (exactDerivedPlusStalkIso I).hom.app X =
      (exactDerivedPlusFactors I).hom.app ((stalkComplex A).obj X) ≫
        DerivedCategory.Plus.Q.map
          (show I.mapCochainComplexPlus.obj ((stalkComplex A).obj X) ⟶
            (stalkComplex B).obj (I.obj X) from
            (CochainComplex.plus B).homMk
              ((HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).hom.app X)) := by
  apply (DerivedCategory.Plus.ι (C := B)).map_injective
  rw [exactDerivedPlusStalkIso_hom_map, Functor.map_comp, exactDerivedPlusFactors_hom_app_map]
  change _ = I.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor A 0).obj X) ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).hom.app X)
  erw [← I.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X,
    Iso.hom_inv_id_app_assoc]

omit [EnoughInjectives A] [EnoughInjectives B] in
@[reassoc]
lemma exactDerivedPlusFactors_inv_stalkIso_hom (X : A) :
    (exactDerivedPlusFactors I).inv.app ((stalkComplex A).obj X) ≫
      (exactDerivedPlusStalkIso I).hom.app X =
        DerivedCategory.Plus.Q.map
          (show I.mapCochainComplexPlus.obj ((stalkComplex A).obj X) ⟶
            (stalkComplex B).obj (I.obj X) from
            (CochainComplex.plus B).homMk
              ((HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).hom.app X)) := by
  rw [exactDerivedPlusStalkIso_app, Iso.inv_hom_id_app_assoc]


/-- The exact precomposition comparison agrees with the canonical unit
when evaluated on the coefficient object as a stalk. -/
@[reassoc]
lemma derivedPrecomposition_stalkToDerived (X : A) :
    (stalkToDerived (I ⋙ J)).app X ≫
      (derivedPrecomposition I J).app ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
      J.rightDerivedFunctorPlus.map ((exactDerivedPlusStalkIso I).hom.app X) =
    (stalkToDerived J).app (I.obj X) := by
  let K := (stalkComplex A).obj X
  let L := (stalkComplex B).obj (I.obj X)
  let a : I.mapCochainComplexPlus.obj K ⟶ L := (CochainComplex.plus B).homMk
    ((HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).hom.app X)
  let b : (stalkComplex D).obj (J.obj (I.obj X)) ⟶ (I ⋙ J).mapCochainComplexPlus.obj K :=
    (CochainComplex.plus D).homMk
      ((HomologicalComplex.singleMapHomologicalComplex (I ⋙ J) (.up ℤ) 0).inv.app X)
  let c : (stalkComplex D).obj (J.obj (I.obj X)) ⟶ J.mapCochainComplexPlus.obj L :=
    (CochainComplex.plus D).homMk
      ((HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).inv.app (I.obj X))
  let Q := DerivedCategory.Plus.Q (C := D)
  let R := J.rightDerivedFunctorPlus
  have h : b ≫ J.mapCochainComplexPlus.map a = c := by
    apply (CochainComplex.Plus.ι D).map_injective
    change b.hom ≫ (J.mapHomologicalComplex (.up ℤ)).map a.hom = c.hom
    apply HomologicalComplex.from_single_hom_ext
    change ((HomologicalComplex.singleMapHomologicalComplex (I ⋙ J) (.up ℤ) 0).inv.app X).f 0 ≫
      J.map (((HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).hom.app X).f 0) =
      ((HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).inv.app (I.obj X)).f 0
    rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp only [Functor.comp_map, Category.assoc, ← J.map_comp, Iso.inv_hom_id_map_assoc]
    rfl
  simp only [stalkToDerived, NatTrans.comp_app, whiskerLeft_app, Category.assoc]
  rw [mappedStalkIso_hom_app_literal (I ⋙ J) X, mappedStalkIso_hom_app_literal J (I.obj X)]
  change Q.map b ≫ (I ⋙ J).rightDerivedFunctorPlusUnit.app K ≫
      (derivedPrecomposition I J).app (DerivedCategory.Plus.Q.obj K) ≫
      R.map ((exactDerivedPlusStalkIso I).hom.app X) =
    Q.map c ≫ J.rightDerivedFunctorPlusUnit.app L
  rw [derivedPrecomposition_unit_assoc, cochainPlusCompIso_inv_app, Q.map_id, Category.id_comp,
    ← R.map_comp, exactDerivedPlusFactors_inv_stalkIso_hom]
  have hn := J.rightDerivedFunctorPlusUnit.naturality a
  change Q.map (J.mapCochainComplexPlus.map a) ≫ J.rightDerivedFunctorPlusUnit.app L =
    J.rightDerivedFunctorPlusUnit.app (I.mapCochainComplexPlus.obj K) ≫
      R.map (DerivedCategory.Plus.Q.map a) at hn
  rw [← hn, ← Q.map_comp_assoc, h]

variable {S : ShortComplex A} (hS : S.ShortExact)

private def exactDerivedPlusStalkTriangleIsoι :
    (DerivedCategory.Plus.ι (C := B)).mapTriangle.obj
        ((exactDerivedPlus I).mapTriangle.obj (plusTriangle A hS)) ≅
      (DerivedCategory.Plus.ι (C := B)).mapTriangle.obj (plusTriangle B (hS.map_of_exact I)) :=
  ((Functor.mapTriangleCompIso (exactDerivedPlus I) DerivedCategory.Plus.ι).symm.app _) ≪≫
    ((Functor.mapTriangleIso (exactDerivedPlusCompι I)).app _) ≪≫
    ((Functor.mapTriangleCompIso DerivedCategory.Plus.ι I.mapDerivedCategory).app _) ≪≫
    (I.mapDerivedCategory.mapTriangle.mapIso (plusStalkTriangleInclusionIso hS)) ≪≫
    (exactMapStalkTriangleIso I hS) ≪≫
    (plusStalkTriangleInclusionIso (hS.map_of_exact I)).symm

/-- The exact functor's stalk comparison carries the extension triangle of a
short exact sequence to the extension triangle of its image. -/
def exactDerivedPlusStalkTriangleIso :
    (exactDerivedPlus I).mapTriangle.obj (plusTriangle A hS) ≅
      plusTriangle B (hS.map_of_exact I) :=
  (FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := B)).mapTriangle).preimageIso
    (exactDerivedPlusStalkTriangleIsoι I hS)

omit [EnoughInjectives A] [EnoughInjectives B] in
@[simp]
lemma exactDerivedPlusStalkTriangleIso_hom₁ :
    ((exactDerivedPlusStalkTriangleIso I hS).hom).hom₁ =
      (exactDerivedPlusStalkIso I).hom.app S.X₁ := by
  apply (DerivedCategory.Plus.ι (C := B)).map_injective
  rw [exactDerivedPlusStalkIso_hom_map]
  have h := (FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := B)).mapTriangle).map_preimage
    (exactDerivedPlusStalkTriangleIsoι I hS).hom
  change (DerivedCategory.Plus.ι (C := B)).mapTriangle.map (exactDerivedPlusStalkTriangleIso I hS).hom =
    (exactDerivedPlusStalkTriangleIsoι I hS).hom at h
  change ((DerivedCategory.Plus.ι (C := B)).mapTriangle.map (exactDerivedPlusStalkTriangleIso I hS).hom).hom₁ = _
  rw [h]
  simp [exactDerivedPlusStalkTriangleIsoι, exactDerivedPlusCompι, ObjectProperty.liftCompιIso,
    Functor.mapTriangleCompIso, plusStalkTriangleInclusionIso, exactMapStalkTriangleIso]
  erw [Category.id_comp, Category.comp_id]

omit [EnoughInjectives A] [EnoughInjectives B] in
@[simp]
lemma exactDerivedPlusStalkTriangleIso_hom₃ :
    ((exactDerivedPlusStalkTriangleIso I hS).hom).hom₃ =
      (exactDerivedPlusStalkIso I).hom.app S.X₃ := by
  apply (DerivedCategory.Plus.ι (C := B)).map_injective
  rw [exactDerivedPlusStalkIso_hom_map]
  have h := (FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := B)).mapTriangle).map_preimage
    (exactDerivedPlusStalkTriangleIsoι I hS).hom
  change (DerivedCategory.Plus.ι (C := B)).mapTriangle.map (exactDerivedPlusStalkTriangleIso I hS).hom =
    (exactDerivedPlusStalkTriangleIsoι I hS).hom at h
  change ((DerivedCategory.Plus.ι (C := B)).mapTriangle.map (exactDerivedPlusStalkTriangleIso I hS).hom).hom₃ = _
  rw [h]
  simp [exactDerivedPlusStalkTriangleIsoι, exactDerivedPlusCompι, ObjectProperty.liftCompιIso,
    Functor.mapTriangleCompIso, plusStalkTriangleInclusionIso, exactMapStalkTriangleIso]
  erw [Category.id_comp, Category.comp_id]

/-- The derived comparison evaluated at an ordinary object using the
canonical stalk identifications. -/
def rightValuePrecomposition (n : ℕ) : rightValue (I ⋙ J) n ⟶ I ⋙ rightValue J n :=
  whiskerRight (whiskerLeft (DerivedCategory.Plus.singleFunctor A 0) (derivedPrecomposition I J) ≫
    whiskerRight (exactDerivedPlusStalkIso I).hom J.rightDerivedFunctorPlus)
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ))

/-- The comparison between deriving a composition with an exact first
functor and precomposing the derived values respects the actual boundaries. -/
lemma rightValuePrecomposition_boundary (n : ℕ) :
    rightBoundary (I ⋙ J) hS n ≫ (rightValuePrecomposition I J (n+1)).app S.X₁ =
      (rightValuePrecomposition I J n).app S.X₃ ≫
        rightBoundary J (hS.map_of_exact I) n := by
  let P := plusTriangle A hS
  let R := J.rightDerivedFunctorPlus
  let φ : ((I ⋙ J).rightDerivedFunctorPlus.mapTriangle.obj P) ⟶
      R.mapTriangle.obj (plusTriangle B (hS.map_of_exact I)) :=
    mapTriangleTransformation (derivedPrecomposition I J) P ≫
      (Functor.mapTriangleCompIso (exactDerivedPlus I) R).hom.app P ≫
        R.mapTriangle.map (exactDerivedPlusStalkTriangleIso I hS).hom
  have h₁ : φ.hom₁ = (derivedPrecomposition I J).app P.obj₁ ≫
      R.map ((exactDerivedPlusStalkIso I).hom.app S.X₁) := by
    change (derivedPrecomposition I J).app P.obj₁ ≫ 𝟙 _ ≫
      R.map (exactDerivedPlusStalkTriangleIso I hS).hom.hom₁ = _
    rw [Category.id_comp, exactDerivedPlusStalkTriangleIso_hom₁]
  have h₃ : φ.hom₃ = (derivedPrecomposition I J).app P.obj₃ ≫
      R.map ((exactDerivedPlusStalkIso I).hom.app S.X₃) := by
    change (derivedPrecomposition I J).app P.obj₃ ≫ 𝟙 _ ≫
      R.map (exactDerivedPlusStalkTriangleIso I hS).hom.hom₃ = _
    rw [Category.id_comp, exactDerivedPlusStalkTriangleIso_hom₃]
  have hh := ((DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ_naturality
    φ (n : ℤ) ((n+1 : ℕ) : ℤ) (by omega)).symm
  change rightBoundary (I ⋙ J) hS n ≫
    (DerivedCategory.Plus.homologyFunctor D ((n+1 : ℕ) : ℤ)).map φ.hom₁ =
      (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map φ.hom₃ ≫
        rightBoundary J (hS.map_of_exact I) n at hh
  rw [h₁, h₃] at hh
  exact hh

end ExactDerivedPrecomposition

end ExactPrecompositionProof

section CompLeft
variable {A B C : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [Category C] [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  {F F' : A ⥤ B} (V : B ⥤ C) [F.Additive] [F'.Additive] [V.Additive]

lemma comparisonValue_natural_left (τ : F ⟶ F') :
    comparisonValue F V ≫ whiskerRight τ.rightDerivedFunctorPlus V.rightDerivedFunctorPlus =
      (whiskerRight τ V).rightDerivedFunctorPlus ≫ comparisonValue F' V := by
  apply CategoryTheory.Functor.rightDerived_ext _ (F ⋙ V).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A) _
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [compositionUnit_app_assoc, ← V.rightDerivedFunctorPlus.map_comp,
    NatTrans.rightDerivedFunctorPlus_fac_app, V.rightDerivedFunctorPlus.map_comp]
  have h := V.rightDerivedFunctorPlusUnit.naturality (τ.mapCochainComplexPlus.app K)
  change DerivedCategory.Plus.Q.map
      (V.mapCochainComplexPlus.map (τ.mapCochainComplexPlus.app K)) ≫
      V.rightDerivedFunctorPlusUnit.app (F'.mapCochainComplexPlus.obj K) =
    V.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
      V.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app K))
    at h
  rw [← reassoc_of% h, NatTrans.rightDerivedFunctorPlus_fac_app_assoc, compositionUnit_app]
  congr 2
end CompLeft


section CompIdentity

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (V : A ⥤ B) [V.Additive]

omit [EnoughInjectives A] in
private lemma mappedStalkIso_id_app (X : A) : (mappedStalkIso (𝟭 A)).hom.app X = 𝟙 _ := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [mappedStalkIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.whiskeringRight_preimage_app, Functor.FullyFaithful.map_preimage, id,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    associator_inv_app, associator_hom_app, isoWhiskerRight_hom, whiskerRight_app,
    Iso.symm_hom, Category.id_comp, Category.comp_id, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, NatTrans.id_app]
  rw [HomologicalComplex.singleMapHomologicalComplex_id_inv_app]
  have h : (Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app
      ((HomologicalComplex.single A (.up ℤ) 0).obj X) = 𝟙 _ := rfl
  erw [h, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private def rightDerivedIdentityUnit :
    𝟭 (DerivedCategory.Plus A) ⟶ (𝟭 A).rightDerivedFunctorPlus := by
  let Q := DerivedCategory.Plus.Q (C := A)
  let W := CochainComplex.Plus.quasiIso A
  let R := (𝟭 A).rightDerivedFunctorPlus
  letI : Localization.Lifting Q W Q (𝟭 _) := ⟨Functor.rightUnitor Q⟩
  letI : Localization.Lifting Q W (Q ⋙ R) R := ⟨Iso.refl _⟩
  exact Localization.liftNatTrans Q W Q (Q⋙R) _ _ ((𝟭 A).rightDerivedFunctorPlusUnit)

private lemma rightDerivedIdentityUnit_app (K : CochainComplex.Plus A) :
    (rightDerivedIdentityUnit (A := A)).app (DerivedCategory.Plus.Q.obj K) =
      (𝟭 A).rightDerivedFunctorPlusUnit.app K := by
  simp [rightDerivedIdentityUnit, Localization.liftNatTrans_app, Localization.Lifting.iso]

lemma comparisonValue_id_left (X : A) :
    (comparisonValue (𝟭 A) V).app ((DerivedCategory.Plus.singleFunctor A 0).obj X) =
    V.rightDerivedFunctorPlus.map ((stalkToDerived (𝟭 A)).app X) := by
  have h : comparisonValue (𝟭 A) V =
      whiskerRight rightDerivedIdentityUnit V.rightDerivedFunctorPlus := by
    apply CategoryTheory.Functor.rightDerived_ext _ ((𝟭 A) ⋙ V).rightDerivedFunctorPlusUnit
      (CochainComplex.Plus.quasiIso A) _
    apply NatTrans.ext
    funext K
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    rw [compositionUnit_app, rightDerivedIdentityUnit_app]
    rfl
  rw [h]
  change V.rightDerivedFunctorPlus.map (rightDerivedIdentityUnit.app
      (DerivedCategory.Plus.Q.obj ((stalkComplex A).obj X))) = _
  rw [rightDerivedIdentityUnit_app]
  simp only [stalkToDerived, NatTrans.comp_app, whiskerLeft_app, mappedStalkIso_id_app]
  erw [Category.id_comp]

end CompIdentity


section ExactInflationFactor

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (I : A ⥤ B) (F : B ⥤ A) (V : A ⥤ C) [I.Additive] [F.Additive] [V.Additive]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]

private lemma derivedPrecomposition_assoc :
    comparisonValue (I ⋙ F) V ≫ whiskerRight (derivedPrecomposition I F) V.rightDerivedFunctorPlus =
      derivedPrecomposition I (F ⋙ V) ≫ whiskerLeft (exactDerivedPlus I) (comparisonValue F V) := by
  apply CategoryTheory.Functor.rightDerived_ext _ ((I ⋙ F) ⋙ V).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A) _
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [compositionUnit_app_assoc, ← V.rightDerivedFunctorPlus.map_comp, derivedPrecomposition_unit,
    cochainPlusCompIso_inv_app I F K, CategoryTheory.Functor.map_id, Category.id_comp, V.rightDerivedFunctorPlus.map_comp]
  change _ = (I ⋙ (F ⋙ V)).rightDerivedFunctorPlusUnit.app K ≫ _
  rw [derivedPrecomposition_unit_assoc, cochainPlusCompIso_inv_app I (F ⋙ V) K, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (comparisonValue F V).naturality ((exactDerivedPlusFactors I).inv.app K)
  change (F ⋙ V).rightDerivedFunctorPlus.map ((exactDerivedPlusFactors I).inv.app K) ≫
      (comparisonValue F V).app ((exactDerivedPlus I).obj (DerivedCategory.Plus.Q.obj K)) =
    (comparisonValue F V).app (DerivedCategory.Plus.Q.obj (I.mapCochainComplexPlus.obj K)) ≫
      V.rightDerivedFunctorPlus.map
        (F.rightDerivedFunctorPlus.map ((exactDerivedPlusFactors I).inv.app K)) at hn
  rw [hn, compositionUnit_app_assoc]
  rfl

private lemma firstEdge_compare_exactPrecomposition (α : 𝟭 A ⟶ I ⋙ F) (X : A) :
    (whiskerRight α V).rightDerivedFunctorPlus.app ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
      (derivedPrecomposition I (F ⋙ V)).app ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
      (F ⋙ V).rightDerivedFunctorPlus.map ((exactDerivedPlusStalkIso I).hom.app X) ≫
      (comparisonValue F V).app ((DerivedCategory.Plus.singleFunctor B 0).obj (I.obj X)) =
    V.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor A 0).map (α.app X) ≫ (stalkToDerived F).app (I.obj X)) := by
  let P := (DerivedCategory.Plus.singleFunctor A 0).obj X
  let Q := (DerivedCategory.Plus.singleFunctor B 0).obj (I.obj X)
  let R := (exactDerivedPlus I).obj P
  let L := V.rightDerivedFunctorPlus
  let s := (exactDerivedPlusStalkIso I).hom.app X
  have hs' := (comparisonValue F V).naturality s
  change _ ≫ (comparisonValue F V).app Q =
    (comparisonValue F V).app R ≫ L.map (F.rightDerivedFunctorPlus.map s) at hs'
  have ha := congrArg (fun t => t.app P) (derivedPrecomposition_assoc I F V)
  change (comparisonValue (I ⋙ F) V).app P ≫ L.map ((derivedPrecomposition I F).app P) =
    (derivedPrecomposition I (F ⋙ V)).app P ≫ (comparisonValue F V).app R at ha
  have hn := congrArg (fun t => t.app P) (comparisonValue_natural_left V α)
  change (comparisonValue (𝟭 A) V).app P ≫ L.map (α.rightDerivedFunctorPlus.app P) =
    (whiskerRight α V).rightDerivedFunctorPlus.app P ≫ (comparisonValue (I ⋙ F) V).app P at hn
  rw [hs', ← reassoc_of% ha, ← reassoc_of% hn]
  erw [comparisonValue_id_left V X]
  simp only [← L.map_comp]
  change L.map ((stalkToDerived (𝟭 A)).app X) ≫ L.map _ = L.map _
  rw [← L.map_comp]
  congr 1
  have hα := stalkToDerived_natural (𝟭 A) (I ⋙ F) α X
  change (stalkToDerived (𝟭 A)).app X ≫ α.rightDerivedFunctorPlus.app P =
    (DerivedCategory.Plus.singleFunctor A 0).map (α.app X) ≫ (stalkToDerived (I ⋙ F)).app X at hα
  rw [reassoc_of% hα, derivedPrecomposition_stalkToDerived I F X]

end ExactInflationFactor


section CohomologicalPrecomposition
variable {A B C : Type*} [Category A] [Abelian A] [Category B] [Abelian B] [Category C] [Abelian C]
lemma shortExact_map_of_finiteLimitsColimits (U : A ⥤ B) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {S : ShortComplex A} (h : S.ShortExact) : (S.map U).ShortExact := by
  let := h.mono_f
  let := h.epi_g
  exact h.map U

/-- Pull a cohomological system back along an exact coefficient functor. -/
def precomposeCohomological (U : A ⥤ B) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (T : CohomologicalSystem B C) : CohomologicalSystem A C where
  value n := U ⋙ T.value n
  δ h n := T.δ (shortExact_map_of_finiteLimitsColimits U h) n

lemma isCohomological_precompose (U : A ⥤ B) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {T : CohomologicalSystem B C} (h : IsCohomological T) :
    IsCohomological (precomposeCohomological U T) where
  additive n := by
    let := h.additive n
    change (U ⋙ T.value n).Additive
    infer_instance
  naturality hS hS' f n := h.naturality (shortExact_map_of_finiteLimitsColimits U hS) (shortExact_map_of_finiteLimitsColimits U hS') (U.mapShortComplex.map f) n
  exact₁ hS n := h.exact₁ (shortExact_map_of_finiteLimitsColimits U hS) n
  exact₂ hS n := h.exact₂ (shortExact_map_of_finiteLimitsColimits U hS) n
  exact₃ hS n := h.exact₃ (shortExact_map_of_finiteLimitsColimits U hS) n
  mono_zero hS := h.mono_zero (shortExact_map_of_finiteLimitsColimits U hS)


end CohomologicalPrecomposition


section InflationIdentification

private abbrev I := inflation.{u,v,w} k G N
private abbrev F := subgroupInvariants.{u,v,w} k G N
private abbrev V := quotientInvariants.{u,v,w} k G N
private abbrev W := totalInvariants.{u,v,w} k G N
private abbrev adj := inflationInvariantsAdjunction.{u,v,w} k G N

/-- First apply inflation to a quotient representation, using the unit of the
inflation and subgroup-invariants adjunction. -/
private def derivedInflationQuotient
    (P : Package (F.{u,v,w} k G N) (V.{u,v,w} k G N)) (n : ℕ) :
    rightValue (V.{u,v,w} k G N) n ⟶ I.{u,v,w} k G N ⋙ rightValue (W.{u,v,w} k G N) n :=
  whiskerRight (adj.{u,v,w} k G N).unit (rightValue (V.{u,v,w} k G N) n) ≫
    whiskerLeft (I.{u,v,w} k G N) (derivedFirstEdge _ _ P n)

private def barInflationQuotient :
    repHomogeneousFunctor.{u,v,w} k (G ⧸ N) ⟶ I.{u,v,w} k G N ⋙ repHomogeneousFunctor.{u,v,w} k G :=
  whiskerRight (adj.{u,v,w} k G N).unit (repHomogeneousFunctor.{u,v,w} k (G ⧸ N)) ≫
    whiskerLeft (I.{u,v,w} k G N) (inflationCochain.{u,v,w} k G N)

private lemma inflation_from_normalization (C : CohomologyModels.{u,v,w} k G N)
    (P : Package (F.{u,v,w} k G N) (V.{u,v,w} k G N))
    (hδ : ∀ {S : ShortComplex (Rep.{max u v w} k (G ⧸ N))} (hS : S.ShortExact) (n : ℕ),
      rightBoundary (V.{u,v,w} k G N) hS n ≫
        (derivedInflationQuotient.{u,v,w} k G N P (n+1)).app S.X₁ =
      (derivedInflationQuotient.{u,v,w} k G N P n).app S.X₃ ≫
        rightBoundary (W.{u,v,w} k G N) (shortExact_map_of_finiteLimitsColimits
          (I.{u,v,w} k G N) hS) n)
    (h₀ : ∀ X (m : (V.{u,v,w} k G N).obj X),
      ((derivedInflationQuotient.{u,v,w} k G N P 0).app X).hom
        (((degreeZeroUnit (V.{u,v,w} k G N)).app X).hom m) =
      (((degreeZeroUnit (W.{u,v,w} k G N)).app ((I.{u,v,w} k G N).obj X)).hom
        (((V.{u,v,w} k G N).map ((adj.{u,v,w} k G N).unit.app X)).hom m))) :
    ∀ n, (isoWhiskerLeft (F.{u,v,w} k G N) (C.quotientDerived n)).hom ≫
        whiskerRight (inflationCochain.{u,v,w} k G N) (HomologicalComplex.homologyFunctor _ (.up ℕ) n) =
      derivedFirstEdge (F.{u,v,w} k G N) (V.{u,v,w} k G N) P n ≫ (C.totalDerived n).hom := by
  let L := I.{u,v,w} k G N
  let FN := F.{u,v,w} k G N
  let Q := V.{u,v,w} k G N
  let Z := W.{u,v,w} k G N
  let A := adj.{u,v,w} k G N
  let Hₙ (n : ℕ) := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n
  let S := rightSystem Q
  let T := precomposeCohomological L (rightSystem Z)
  let D := normSystem.{u,v,w} k G L
  let B := normSystem.{u,v,w} k (G ⧸ N) (𝟭 _)
  have hS : IsCohomological S := UniversalDeltaFunctors.rightDelta _ _ Q
  have hD : IsCohomological D := normSystem_cohomological k G L
  have hvanish (J : Rep.{max u v w} k (G ⧸ N)) [Injective J] (n : ℕ) :
      IsZero ((S.value (n+1)).obj J) := ClassicalDerivedValues.rightInjectiveVanishing _ _ Q J n
  have hU := UniversalDeltaFunctors.universal_of_injective_vanishing S hS @hvanish
  let d : CohomologicalMorphism S T := ⟨derivedInflationQuotient.{u,v,w} k G N P, hδ⟩
  let c : CohomologicalMorphism T D :=
    { component n := whiskerLeft L (C.totalDerived n).hom
      comm hS n := by
        obtain ⟨_, h⟩ := C.total_connectors
        exact h (shortExact_map_of_finiteLimitsColimits L hS) n }
  let b : CohomologicalMorphism S B :=
    { component n := (C.quotientDerived n).hom
      comm hS n := by obtain ⟨_, h⟩ := C.quotient_connectors; exact h hS n }
  let r : CohomologicalMorphism B D :=
    { component n := whiskerRight (barInflationQuotient.{u,v,w} k G N) (Hₙ n)
      comm hS n := cochainTransformation_connectors (barInflationQuotient.{u,v,w} k G N)
        (normExact k (G ⧸ N) hS) (normExact_comp k G L hS) n }
  let left := GroupLowDegreesAndCoefficients.deltaComposition d c
  let right := GroupLowDegreesAndCoefficients.deltaComposition b r
  have hzero : left.component 0 = right.component 0 := by
    apply NatTrans.ext
    funext X
    apply (cancel_epi ((degreeZeroIso Q).hom.app X)).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let a := ((Q.map (A.unit.app X)).hom x)
    obtain ⟨z, hz, hz₀⟩ := C.quotient_augmentation X x
    obtain ⟨y, hy, hy₀⟩ := C.total_augmentation (L.obj X) a
    let K := (repHomogeneousFunctor.{u,v,w} k (G ⧸ N)).obj X
    let J := (repHomogeneousFunctor.{u,v,w} k G).obj (L.obj X)
    let R := (barInflationQuotient.{u,v,w} k G N).app X
    change ((C.totalDerived 0).hom.app (L.obj X)).hom
      (((derivedInflationQuotient.{u,v,w} k G N P 0).app X).hom (((degreeZeroUnit Q).app X).hom x)) =
      (HomologicalComplex.homologyMap R 0).hom
        (((C.quotientDerived 0).hom.app X).hom (((degreeZeroUnit Q).app X).hom x))
    rw [h₀ X x]
    change ((C.totalDerived 0).hom.app (L.obj X)).hom (((degreeZeroUnit Z).app (L.obj X)).hom a) = _
    erw [hy₀, hz₀]
    have hπ := congrArg (fun f => f.hom z) (HomologicalComplex.homologyπ_naturality R 0)
    change _ = (HomologicalComplex.homologyMap R 0).hom ((K.homologyπ 0).hom z)
    change (HomologicalComplex.homologyMap R 0).hom ((K.homologyπ 0).hom z) =
      (J.homologyπ 0).hom ((HomologicalComplex.cyclesMap R 0).hom z) at hπ
    rw [hπ]
    congr 1
    apply (ModuleCat.mono_iff_injective (J.iCycles 0)).mp inferInstance
    have hi := congrArg (fun f => f.hom z) (HomologicalComplex.cyclesMap_i R 0)
    change (J.iCycles 0).hom ((HomologicalComplex.cyclesMap R 0).hom z) =
      (R.f 0).hom ((K.iCycles 0).hom z) at hi
    change (J.iCycles 0).hom y = (J.iCycles 0).hom ((HomologicalComplex.cyclesMap R 0).hom z)
    rw [hi]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change ((J.iCycles 0).hom y).hom (GroupBar.Large.single.{u,v,w} k G c 1) =
      ((R.f 0).hom ((K.iCycles 0).hom z)).hom (GroupBar.Large.single.{u,v,w} k G c 1)
    let cQ : Fin 1 → (G ⧸ N) := fun i => QuotientGroup.mk' N (c i)
    have hR := inflationCochain_formula.{u,v,w} k G N (L.obj X) 0
      (((K.iCycles 0).hom z) ≫ A.unit.app X) c
    change ((R.f 0).hom ((K.iCycles 0).hom z)).hom (GroupBar.Large.single.{u,v,w} k G c 1) =
      ((A.unit.app X).hom (((K.iCycles 0).hom z).hom (GroupBar.Large.single.{u,v,w} k (G ⧸ N) cQ 1))).val
      at hR
    erw [hy, hR, hz]
    rfl
  obtain ⟨w, _, hw⟩ := hU D hD (right.component 0)
  have h := (hw left hzero).trans (hw right rfl).symm
  intro n
  apply NatTrans.ext
  funext M
  let μ : L.obj (FN.obj M) ⟶ M := A.counit.app M
  let e := derivedFirstEdge FN Q P n
  let q := (C.quotientDerived n).hom
  let z := (C.totalDerived n).hom
  let j := whiskerRight (inflationCochain.{u,v,w} k G N) (Hₙ n)
  have h' := congrArg (fun a : CohomologicalMorphism S D => (a.component n).app (FN.obj M)) h
  simp only [left, right, GroupLowDegreesAndCoefficients.deltaComposition, d, c, b, r,
    derivedInflationQuotient, barInflationQuotient, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, Category.assoc] at h'
  rw [(Hₙ n).map_comp] at h'
  change (rightValue Q n).map (A.unit.app (FN.obj M)) ≫ e.app (L.obj (FN.obj M)) ≫ z.app (L.obj (FN.obj M)) =
    q.app (FN.obj M) ≫ (repHomogeneousCohomology.{u,v,w} k (G ⧸ N) n).map (A.unit.app (FN.obj M)) ≫
      j.app (L.obj (FN.obj M)) at h'
  let η : FN.obj M ⟶ FN.obj (L.obj (FN.obj M)) := A.unit.app (FN.obj M)
  have htri : η ≫ FN.map μ = 𝟙 (FN.obj M) := A.right_triangle_components M
  have he := e.naturality μ
  have hz := z.naturality μ
  have hj := j.naturality μ
  change (rightValue Z n).map μ ≫ z.app M =
    z.app (L.obj (FN.obj M)) ≫ (repHomogeneousCohomology.{u,v,w} k G n).map μ at hz
  change (rightValue Q n).map (FN.map μ) ≫ e.app M =
    e.app (L.obj (FN.obj M)) ≫ (rightValue Z n).map μ at he
  change (repHomogeneousCohomology.{u,v,w} k (G ⧸ N) n).map (FN.map μ) ≫ j.app M =
    j.app (L.obj (FN.obj M)) ≫ (repHomogeneousCohomology.{u,v,w} k G n).map μ at hj
  have h'' := congrArg (fun a => a ≫ (repHomogeneousCohomology.{u,v,w} k G n).map μ) h'
  simp only [Category.assoc] at h''
  change (rightValue Q n).map η ≫ e.app (L.obj (FN.obj M)) ≫ z.app (L.obj (FN.obj M)) ≫ _ =
    q.app (FN.obj M) ≫ (repHomogeneousCohomology.{u,v,w} k (G ⧸ N) n).map η ≫
      j.app (L.obj (FN.obj M)) ≫ _ at h''
  rw [← hz, ← reassoc_of% he, ← hj] at h''
  change (rightValue Q n).map η ≫ (rightValue Q n).map (FN.map μ) ≫ e.app M ≫ z.app M =
    q.app (FN.obj M) ≫ (repHomogeneousCohomology.{u,v,w} k (G ⧸ N) n).map η ≫
      (repHomogeneousCohomology.{u,v,w} k (G ⧸ N) n).map (FN.map μ) ≫ j.app M at h''
  simp only [← CategoryTheory.Functor.map_comp_assoc, htri, CategoryTheory.Functor.map_id, Category.id_comp] at h''
  exact h''.symm

end InflationIdentification


section InflationComparison

private lemma derivedInflationQuotient_degreeZero
    (P : Package (F.{u,v,w} k G N) (V.{u,v,w} k G N))
    (X : Rep.{max u v w} k (G ⧸ N)) (m : (V.{u,v,w} k G N).obj X) :
    ((derivedInflationQuotient.{u,v,w} k G N P 0).app X).hom
      (((degreeZeroUnit (V.{u,v,w} k G N)).app X).hom m) =
    (((degreeZeroUnit (W.{u,v,w} k G N)).app ((I.{u,v,w} k G N).obj X)).hom
      (((V.{u,v,w} k G N).map ((adj.{u,v,w} k G N).unit.app X)).hom m)) := by
  let Q := V.{u,v,w} k G N
  let L := I.{u,v,w} k G N
  let e := (adj.{u,v,w} k G N).unit.app X
  let d := derivedFirstEdge (F.{u,v,w} k G N) Q P 0
  have h := (degreeZeroUnit Q).naturality e
  have h' : (degreeZeroUnit Q).app X ≫ (derivedInflationQuotient.{u,v,w} k G N P 0).app X =
      Q.map e ≫ (degreeZeroUnit (W.{u,v,w} k G N)).app (L.obj X) := by
    change (degreeZeroUnit Q).app X ≫ (rightValue Q 0).map e ≫ d.app (L.obj X) = _
    rw [← reassoc_of% h, derivedFirstEdge_degreeZeroUnit]
  exact congrArg (fun f => f.hom m) h'


private lemma derivedInflationQuotient_precomposition
    (P : Package (F.{u,v,w} k G N) (V.{u,v,w} k G N)) (n : ℕ) :
    derivedInflationQuotient.{u,v,w} k G N P n =
      derivedValueTransformation (V.{u,v,w} k G N) (I.{u,v,w} k G N ⋙ W.{u,v,w} k G N)
        (whiskerRight (adj.{u,v,w} k G N).unit (V.{u,v,w} k G N)) n ≫
      rightValuePrecomposition (I.{u,v,w} k G N) (W.{u,v,w} k G N) n := by
  let Q := V.{u,v,w} k G N
  let L := I.{u,v,w} k G N
  let FN := F.{u,v,w} k G N
  let Z := W.{u,v,w} k G N
  let A := adj.{u,v,w} k G N
  let := P.comparison_isIso
  let : IsIso (comparisonValue FN Q) := NatIso.isIso_of_isIso_app _
  apply NatTrans.ext
  funext X
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v w} k) (n : ℤ)
  let SX := (DerivedCategory.Plus.singleFunctor (Rep.{max u v w} k (G ⧸ N)) 0)
  let SY := (DerivedCategory.Plus.singleFunctor (Rep.{max u v w} k G) 0)
  let c := (asIso (comparisonValue FN Q)).app (SY.obj (L.obj X))
  have h := firstEdge_compare_exactPrecomposition L FN Q A.unit X
  have h₁ :
      ((whiskerRight A.unit Q).rightDerivedFunctorPlus.app (SX.obj X) ≫
        (derivedPrecomposition L Z).app (SX.obj X) ≫
        Z.rightDerivedFunctorPlus.map ((exactDerivedPlusStalkIso L).hom.app X)) ≫ c.hom =
      Q.rightDerivedFunctorPlus.map (SX.map (A.unit.app X) ≫ (stalkToDerived FN).app (L.obj X)) := by
    simpa only [Category.assoc, Z, FN, Q, L, SX, SY, c, Iso.app_hom, asIso_hom] using h
  have hh := congrArg H.map ((Iso.comp_inv_eq c).2 h₁.symm)
  change H.map (Q.rightDerivedFunctorPlus.map (SX.map (A.unit.app X))) ≫
      (H.map (Q.rightDerivedFunctorPlus.map ((stalkToDerived FN).app (L.obj X)))) ≫ H.map c.inv =
    H.map ((whiskerRight A.unit Q).rightDerivedFunctorPlus.app (SX.obj X)) ≫
      H.map ((derivedPrecomposition L Z).app (SX.obj X) ≫
        Z.rightDerivedFunctorPlus.map ((exactDerivedPlusStalkIso L).hom.app X))
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using hh


private lemma derivedInflationQuotient_connectors
    (P : Package (F.{u,v,w} k G N) (V.{u,v,w} k G N))
    {S : ShortComplex (Rep.{max u v w} k (G ⧸ N))} (hS : S.ShortExact) (n : ℕ) :
    rightBoundary (V.{u,v,w} k G N) hS n ≫
        (derivedInflationQuotient.{u,v,w} k G N P (n+1)).app S.X₁ =
      (derivedInflationQuotient.{u,v,w} k G N P n).app S.X₃ ≫
        rightBoundary (W.{u,v,w} k G N) (shortExact_map_of_finiteLimitsColimits
          (I.{u,v,w} k G N) hS) n := by
  let J := I.{u,v,w} k G N
  let Q := V.{u,v,w} k G N
  let Z := W.{u,v,w} k G N
  let τ : Q ⟶ J ⋙ Z := whiskerRight (adj.{u,v,w} k G N).unit Q
  rw [derivedInflationQuotient_precomposition, derivedInflationQuotient_precomposition]
  simp only [NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% (rightBoundary_derivedValueTransformation Q (J ⋙ Z) τ hS n),
    rightValuePrecomposition_boundary]

end InflationComparison

/-- The Lyndon–Hochschild–Serre spectral sequence for a normal subgroup.
Both ordinary edge maps and the transgression use the same object-case
Grothendieck spectral sequence and the same normalized bar coordinates. -/
theorem lyndonHochschildSerre : Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre.FullStatement.{u,v,w} k G N := by
  obtain ⟨P, ⟨E⟩⟩ := composition.{u,v,w} k G N
  obtain ⟨C⟩ := models.{u,v,w} k G N
  refine assemble C E (identifyFilteredGroupEdges C E (ordinaryRestriction C)
    (inflationCochain.{u,v,w} k G N) (inflationCochain_formula.{u,v,w} k G N) ?_ (ordinaryRestriction_eq C E))
  exact inflation_from_normalization k G N C P (derivedInflationQuotient_connectors k G N P)
    (derivedInflationQuotient_degreeZero k G N P)

end AdvancedHomologicalAlgebra.GroupHochschildSerre
