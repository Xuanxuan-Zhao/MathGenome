import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ULift
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Sheafify

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TopologicalSpace Opposite Topology

universe u

namespace RepTheorySurvey.Geometric.Analytic

abbrev Coeff := ModuleCat.{u} ℚ
instance : PreservesFilteredColimits (CategoryTheory.forget Coeff.{u}) := by
  let G := forget₂ Coeff.{u} AddCommGrpCat.{u}
  have : PreservesFilteredColimits G := by
    constructor
    intro J _ _
    exact ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone
      (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
      (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ G))⟩
  exact comp_preservesFilteredColimits G (CategoryTheory.forget AddCommGrpCat.{u})

instance : IsGrothendieckAbelian.{u} Coeff.{u} where
  ab5OfSize := ⟨fun J _ _ =>
    HasExactColimitsOfShape.domain_of_functor J (forget₂ Coeff.{u} AddCommGrpCat.{u})⟩

abbrev Sheaves (X : TopCat.{u}) := X.Sheaf Coeff.{u}
instance (X : TopCat.{u}) : HasDerivedCategory.{u + 1} (Sheaves X) :=
  HasDerivedCategory.standard _

abbrev Derived (X : TopCat.{u}) := DerivedCategory (Sheaves X)
abbrev BoundedBelow (X : TopCat.{u}) := DerivedCategory.Plus (Sheaves X)

def constant (X : TopCat.{u}) (V : Coeff.{u}) : Sheaves X :=
  (constantSheaf (Opens.grothendieckTopology X) _).obj V

def rational (X : TopCat.{u}) : Sheaves X := constant X (ModuleCat.of ℚ (ULift.{u} ℚ))

def stalk {X : TopCat.{u}} (x : X) : Sheaves X ⥤ Coeff.{u} :=
  TopCat.Sheaf.forget _ X ⋙ TopCat.Presheaf.stalkFunctor _ x

instance {X : TopCat.{u}} (x : X) : (stalk x).Additive := by
  unfold stalk
  infer_instance

abbrev inverseImage {X Y : TopCat.{u}} (f : X ⟶ Y) : Sheaves Y ⥤ Sheaves X :=
  TopCat.Sheaf.pullback _ f

abbrev directImage {X Y : TopCat.{u}} (f : X ⟶ Y) : Sheaves X ⥤ Sheaves Y :=
  TopCat.Sheaf.pushforward _ f

def inverseDirectAdjunction {X Y : TopCat.{u}} (f : X ⟶ Y) :
    inverseImage f ⊣ directImage f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction _ f

instance {X Y : TopCat.{u}} (f : X ⟶ Y) : PreservesFiniteLimits (inverseImage f) := by
  have : ReflectsLimits (CategoryTheory.forget Coeff.{u}) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits (TopCat.Presheaf.pullback Coeff.{u} f) := by
    unfold TopCat.Presheaf.pullback
    exact lan_preservesFiniteLimits_of_preservesFiniteLimits Coeff.{u} (Opens.map f)
  have : PreservesFiniteLimits (presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}) :=
    inferInstance
  have : PreservesFiniteLimits
      (TopCat.Presheaf.pullback Coeff.{u} f ⋙
        presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (TopCat.Sheaf.forget Coeff.{u} Y ⋙ TopCat.Presheaf.pullback Coeff.{u} f ⋙
        presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (TopCat.Sheaf.pullbackIso Coeff.{u} f).symm

instance {X Y : TopCat.{u}} (f : X ⟶ Y) : (inverseImage f).Additive :=
  Functor.additive_of_preserves_binary_products _

instance {X Y : TopCat.{u}} (f : X ⟶ Y) : (directImage f).Additive :=
  Functor.additive_of_preserves_binary_products _

def derivedDirectImage {X Y : TopCat.{u}} (f : X ⟶ Y) :
    BoundedBelow X ⥤ BoundedBelow Y :=
  (directImage f).rightDerivedFunctorPlus

def derivedInverseImage {X Y : TopCat.{u}} (f : X ⟶ Y) : Derived Y ⥤ Derived X :=
  (inverseImage f).mapDerivedCategory

abbrev cohomology (X : TopCat.{u}) (n : ℤ) : Derived X ⥤ Sheaves X :=
  DerivedCategory.homologyFunctor _ n

def shiftCohomology (X : TopCat.{u}) (a b : ℤ) :
    shiftFunctor (Derived X) b ⋙ cohomology X a ≅ cohomology X (a + b) :=
  (cohomology X 0).shiftIso b a (a + b) (add_comm _ _)

def openInclusion {X : TopCat.{u}} (U : Opens X) : TopCat.of U ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def closedInclusion {X : TopCat.{u}} (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def complementOpen {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The stalk map obtained by applying the inverse/direct image unit and taking a germ. -/
def inverseImageStalkMap {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Sheaves Y) (x : X) :
    (stalk (f x)).obj F ⟶ (stalk x).obj ((inverseImage f).obj F) :=
  (stalk (f x)).map ((inverseDirectAdjunction f).unit.app F) ≫
    TopCat.Presheaf.stalkPushforward _ f ((inverseImage f).obj F).obj x

private theorem stalkPushforward_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : X.Presheaf Coeff.{u}} (v : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor Coeff.{u} (f x)).map
        ((TopCat.Presheaf.pushforward Coeff.{u} f).map v) ≫
      G.stalkPushforward _ f x =
    F.stalkPushforward _ f x ≫ (TopCat.Presheaf.stalkFunctor Coeff.{u} x).map v := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc U (f x) hU _ _,
    TopCat.Presheaf.stalkPushforward_germ, TopCat.Presheaf.stalkPushforward_germ_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

instance {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Sheaves Y) (x : X) :
    IsIso (inverseImageStalkMap f F x) := by
  let c := TopCat.Sheaf.pullbackIso Coeff.{u} f
  let t := (stalk x).map (c.hom.app F)
  suffices IsIso (inverseImageStalkMap f F x ≫ t) by
    have : IsIso t := inferInstance
    exact IsIso.of_isIso_comp_right _ t
  unfold inverseImageStalkMap
  dsimp only [t]
  rw [Category.assoc]
  erw [← stalkPushforward_naturality f (c.hom.app F).1 x]
  change IsIso ((stalk (f x)).map ((inverseDirectAdjunction f).unit.app F) ≫
    (stalk (f x)).map ((directImage f).map (c.hom.app F)) ≫ _)
  rw [← Functor.map_comp_assoc]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (inverseDirectAdjunction f)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
      Coeff.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) F
  change _ ≫ (directImage f).map (c.hom.app F) = _ at hu
  rw [hu]
  let P := TopCat.Presheaf.pullback Coeff.{u} f
  let ψ := CategoryTheory.toSheafify (Opens.grothendieckTopology X) (P.obj F.obj)
  change IsIso ((TopCat.Presheaf.stalkFunctor Coeff.{u} (f x)).map
    ((TopCat.Presheaf.pullbackPushforwardAdjunction Coeff.{u} f).unit.app F.obj ≫
      (TopCat.Presheaf.pushforward Coeff.{u} f).map ψ) ≫ _)
  rw [Functor.map_comp, Category.assoc]
  erw [stalkPushforward_naturality f ψ x]
  rw [← Category.assoc]
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    x Coeff.{u} (P.obj F.obj)
  change IsIso ((TopCat.Presheaf.stalkPullbackIso Coeff.{u} f F.obj x).hom ≫ _)
  infer_instance

def inverseImageStalkIso {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Sheaves Y) (x : X) :
    (stalk (f x)).obj F ≅ (stalk x).obj ((inverseImage f).obj F) :=
  asIso (inverseImageStalkMap f F x)

/-- Vanishing of the stalks off a closed subset. -/
def SupportedOn {X : TopCat.{u}} (Z : Set X) (F : Sheaves X) : Prop :=
  ∀ x : X, x ∉ Z → IsZero ((stalk x).obj F)

theorem closedDirectImage_supported {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (F : Sheaves (TopCat.of Z)) : SupportedOn Z ((directImage (closedInclusion Z)).obj F) := by
  intro x hx
  rw [IsZero.iff_id_eq_zero]
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  let W := U ⊓ complementOpen Z hZ
  have hW : x ∈ W := ⟨hU, hx⟩
  have hWempty : (Opens.map (closedInclusion Z)).obj W = ⊥ := by
    ext z
    exact ⟨fun h => h.2 z.property, False.elim⟩
  let P : X.Presheaf Coeff.{u} := ((directImage (closedInclusion Z)).obj F).obj
  have hz : IsZero (P.obj (op W)) := by
    change IsZero (F.obj.obj (op ((Opens.map (closedInclusion Z)).obj W)))
    exact (isZero_zero _).of_iso
      ((F.isTerminalOfEqEmpty hWempty).uniqueUpToIso (isZero_zero _).isTerminal)
  change P.germ U x hU ≫ 𝟙 (P.stalk x) = P.germ U x hU ≫ 0
  rw [Category.comp_id, comp_zero, ← P.germ_res (homOfLE inf_le_left : W ⟶ U) x hW]
  rw [hz.eq_of_tgt (P.map (homOfLE inf_le_left : W ⟶ U).op) 0, zero_comp]

private theorem inverseDirectUnit_stalk_isIso {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hi : IsInducing f) (F : Sheaves Y) (x : X) :
    IsIso ((stalk (f x)).map ((inverseDirectAdjunction f).unit.app F)) := by
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Coeff.{u} hi
    ((inverseImage f).obj F).obj x
  have : IsIso ((stalk (f x)).map ((inverseDirectAdjunction f).unit.app F) ≫
      TopCat.Presheaf.stalkPushforward _ f ((inverseImage f).obj F).obj x) :=
    inferInstanceAs (IsIso (inverseImageStalkMap f F x))
  exact IsIso.of_isIso_comp_right _ (TopCat.Presheaf.stalkPushforward _ f
    ((inverseImage f).obj F).obj x)

theorem closedInverseDirectUnit_isIso {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (F : Sheaves X) (hF : SupportedOn Z F) :
    IsIso ((inverseDirectAdjunction (closedInclusion Z)).unit.app F) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro x
  by_cases hx : x ∈ Z
  · exact inverseDirectUnit_stalk_isIso (f := closedInclusion Z) IsInducing.subtypeVal F ⟨x, hx⟩
  · exact isIso_of_source_target_iso_zero _ (hF x hx).isoZero
      (closedDirectImage_supported hZ _ x hx).isoZero

/-- The subsheaf of sections vanishing on the open complement of the closed set. -/
def sectionsWithSupport {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    Sheaves X ⥤ Sheaves X := by
  let r := (inverseDirectAdjunction (openInclusion (complementOpen Z hZ))).unit
  exact
    { obj := fun F => Arrow.mk (r.app F)
      map := fun v => Arrow.homMk v ((inverseImage _ ⋙ directImage _).map v) (r.naturality v) } ⋙ ker (Sheaves X)

def sectionsWithSupportInclusion {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    sectionsWithSupport hZ ⟶ 𝟭 (Sheaves X) :=
  { app := fun F => kernel.ι ((inverseDirectAdjunction
      (openInclusion (complementOpen Z hZ))).unit.app F)
    naturality := by intros; apply kernel.lift_ι }

theorem sectionsWithSupport_supported {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (F : Sheaves X) : SupportedOn Z ((sectionsWithSupport hZ).obj F) := by
  intro x hx
  let j := openInclusion (complementOpen Z hZ)
  let r := (inverseDirectAdjunction j).unit.app F
  have : IsIso ((stalk x).map r) :=
    inverseDirectUnit_stalk_isIso (f := j) IsInducing.subtypeVal F ⟨x, hx⟩
  let k := (sectionsWithSupportInclusion hZ).app F
  have : Mono k := by
    change Mono (kernel.ι r)
    infer_instance
  have : (stalk x).PreservesMonomorphisms := by
    unfold stalk
    infer_instance
  have : Mono ((stalk x).map k) := Functor.map_mono (stalk x) k
  have hzero : (stalk x).map k = 0 := by
    apply (cancel_mono ((stalk x).map r)).mp
    rw [zero_comp, ← Functor.map_comp]
    change (stalk x).map (kernel.ι r ≫ r) = 0
    rw [kernel.condition]
    exact (stalk x).map_zero _ _
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_mono ((stalk x).map k)).mp (by rw [hzero, Category.id_comp, zero_comp])

def extraordinaryInverseImage {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    Sheaves X ⥤ Sheaves (TopCat.of Z) :=
  sectionsWithSupport hZ ⋙ inverseImage (closedInclusion Z)

private def supportedUnitIso {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (F : Sheaves X) :
    (sectionsWithSupport hZ).obj F ≅
      (directImage (closedInclusion Z)).obj ((extraordinaryInverseImage hZ).obj F) :=
  letI := closedInverseDirectUnit_isIso hZ _ (sectionsWithSupport_supported hZ F)
  asIso ((inverseDirectAdjunction (closedInclusion Z)).unit.app
    ((sectionsWithSupport hZ).obj F))

private theorem restriction_zero_of_supported {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (F : Sheaves X) (hF : SupportedOn Z F) :
    IsZero ((inverseImage (openInclusion (complementOpen Z hZ))).obj F) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  exact (hF x.val x.property).of_iso (inverseImageStalkIso _ F x).symm

private def supportHomEquiv {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (G : Sheaves (TopCat.of Z)) (F : Sheaves X) :
    ((directImage (closedInclusion Z)).obj G ⟶ F) ≃
      ((directImage (closedInclusion Z)).obj G ⟶ (sectionsWithSupport hZ).obj F) where
  toFun v := kernel.lift _ v (by
    let A := (directImage (closedInclusion Z)).obj G
    let j := openInclusion (complementOpen Z hZ)
    let a := inverseDirectAdjunction j
    have hz := restriction_zero_of_supported hZ A (closedDirectImage_supported hZ G)
    have he := (Functor.map_isZero (directImage j) hz).eq_of_tgt (a.unit.app A) 0
    change (𝟭 (Sheaves X)).map v ≫ a.unit.app F = 0
    rw [a.unit.naturality, he, zero_comp])
  invFun w := w ≫ (sectionsWithSupportInclusion hZ).app F
  left_inv v := kernel.lift_ι _ _ _
  right_inv w := by
    change kernel.lift _ _ _ = w
    apply (cancel_mono (kernel.ι _)).mp
    exact kernel.lift_ι _ _ _

theorem inducedCounit_stalk {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Sheaves X) (x : X) :
    inverseImageStalkMap f ((directImage f).obj F) x ≫
      (stalk x).map ((inverseDirectAdjunction f).counit.app F) =
      TopCat.Presheaf.stalkPushforward _ f F.obj x := by
  let a := inverseDirectAdjunction f
  let v := a.counit.app F
  unfold inverseImageStalkMap
  rw [Category.assoc]
  erw [← stalkPushforward_naturality f v.1 x]
  change (stalk (f x)).map (a.unit.app ((directImage f).obj F)) ≫
    (stalk (f x)).map ((directImage f).map v) ≫ _ = _
  rw [← Functor.map_comp_assoc, a.right_triangle_components]
  simp

theorem inducedCounit_isIso {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
    (F : Sheaves X) : IsIso ((inverseDirectAdjunction f).counit.app F) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro x
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    Coeff.{u} hf F.obj x
  have : IsIso (inverseImageStalkMap f ((directImage f).obj F) x ≫
      (stalk x).map ((inverseDirectAdjunction f).counit.app F)) := by
    rw [inducedCounit_stalk]
    infer_instance
  change IsIso ((stalk x).map ((inverseDirectAdjunction f).counit.app F))
  exact IsIso.of_isIso_comp_left (inverseImageStalkMap f ((directImage f).obj F) x) _

def closedDirectImageFullyFaithful {X : TopCat.{u}} (Z : Set X) :
    (directImage (closedInclusion Z)).FullyFaithful :=
  let a := inverseDirectAdjunction (closedInclusion Z)
  have (F : Sheaves (TopCat.of Z)) : IsIso (a.counit.app F) :=
    inducedCounit_isIso (f := closedInclusion Z) IsInducing.subtypeVal F
  have : IsIso a.counit := NatIso.isIso_of_isIso_app a.counit
  a.fullyFaithfulROfIsIsoCounit

/-- Extension from the closed subspace is left adjoint to supported restriction. -/
def extraordinaryAdjunction {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    directImage (closedInclusion Z) ⊣ extraordinaryInverseImage hZ := by
  let i := closedInclusion Z
  let ff := closedDirectImageFullyFaithful Z
  refine Adjunction.mkOfHomEquiv
    { homEquiv := fun G F => (supportHomEquiv hZ G F).trans
        ((Iso.homCongr (Iso.refl ((directImage i).obj G)) (supportedUnitIso hZ F)).trans
          ff.homEquiv.symm)
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro G' G F v w
    change (((directImage i).map (v ≫ w) ≫ (supportedUnitIso hZ F).inv) ≫
          (sectionsWithSupportInclusion hZ).app F) =
      (directImage i).map v ≫
        (((directImage i).map w ≫ (supportedUnitIso hZ F).inv) ≫
          (sectionsWithSupportInclusion hZ).app F)
    rw [Functor.map_comp]
    simp only [Category.assoc]
  · intro G F F' v w
    let e := fun K => supportedUnitIso hZ K
    have hn : (sectionsWithSupport hZ).map w ≫ (e F').hom =
        (e F).hom ≫ (directImage i).map ((extraordinaryInverseImage hZ).map w) :=
      (inverseDirectAdjunction i).unit.naturality ((sectionsWithSupport hZ).map w)
    apply ff.map_injective
    change (directImage i).map (ff.preimage
      ((supportHomEquiv hZ G F') (v ≫ w) ≫ (e F').hom)) =
      (directImage i).map (ff.preimage ((supportHomEquiv hZ G F) v ≫ (e F).hom) ≫
        (extraordinaryInverseImage hZ).map w)
    rw [Functor.map_comp, ff.map_preimage, ff.map_preimage, Category.assoc, ← hn,
      ← Category.assoc]
    congr 1
    have : Mono ((sectionsWithSupportInclusion hZ).app F') :=
      inferInstanceAs (Mono (kernel.ι ((inverseDirectAdjunction
        (openInclusion (complementOpen Z hZ))).unit.app F')))
    apply (cancel_mono ((sectionsWithSupportInclusion hZ).app F')).mp
    rw [Category.assoc, (sectionsWithSupportInclusion hZ).naturality]
    exact (supportHomEquiv hZ G F').left_inv (v ≫ w) |>.trans
      (by
        have he : (supportHomEquiv hZ G F) v ≫ (sectionsWithSupportInclusion hZ).app F = v :=
          (supportHomEquiv hZ G F).left_inv v
        rw [← Category.assoc, he]
        rfl)

instance {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    (extraordinaryInverseImage hZ).IsRightAdjoint :=
  (extraordinaryAdjunction hZ).isRightAdjoint

instance {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    (extraordinaryInverseImage hZ).Additive :=
  Functor.additive_of_preserves_binary_products _

def derivedExtraordinaryInverseImage {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    BoundedBelow X ⥤ BoundedBelow (TopCat.of Z) :=
  (extraordinaryInverseImage hZ).rightDerivedFunctorPlus

def closedExtension {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    Derived (TopCat.of Z) ⥤ Derived X := by
  have := (extraordinaryAdjunction hZ).isLeftAdjoint
  exact (directImage (closedInclusion Z)).mapDerivedCategory

def LocallyConstantFiniteRank {X : TopCat.{u}} (F : Sheaves X) : Prop :=
  ∀ x : X, ∃ (U : Opens X), x ∈ U ∧
    ∃ V : Coeff.{u}, Module.Finite ℚ V ∧
      Nonempty ((inverseImage (openInclusion U)).obj F ≅ constant (TopCat.of U) V)

/-- Data exhibiting a stratum as closed inside an open subspace. -/
structure Stratum (X : TopCat.{u}) where
  ambientOpen : Opens X
  subset : Set ambientOpen
  closed : IsClosed subset
  complexDimension : ℕ

abbrev Stratum.space {X : TopCat.{u}} (S : Stratum X) : TopCat.{u} :=
  TopCat.of S.subset

def Stratum.inclusion {X : TopCat.{u}} (S : Stratum X) : S.space ⟶ X :=
  closedInclusion (X := TopCat.of S.ambientOpen) S.subset ≫ openInclusion S.ambientOpen

/-- The locally closed strata form a partition of the space. -/
structure Stratification (X : TopCat.{u}) where
  Index : Type u
  stratum : Index → Stratum X
  partition : ∀ x : X, ∃! s : Index, x ∈ Set.range (stratum s).inclusion

def IsConstructible {X : TopCat.{u}} (P : Stratification X) (F : Derived X) : Prop :=
  (Set.Finite {n : ℤ | ¬ IsZero ((cohomology X n).obj F)}) ∧
    ∀ (s : P.Index) (n : ℤ), LocallyConstantFiniteRank
      ((inverseImage (P.stratum s).inclusion).obj ((cohomology X n).obj F))

abbrev Constructible {X : TopCat.{u}} (P : Stratification X) :=
  (show ObjectProperty (Derived X) from IsConstructible P).FullSubcategory

/-- The exact inverse image on the usual bounded-below derived category. -/
def boundedBelowInverseImage {X Y : TopCat.{u}} (f : X ⟶ Y) :
    BoundedBelow Y ⥤ BoundedBelow X :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ derivedInverseImage f) (by
    rintro ⟨F, n, K, e, hK⟩
    let P := inverseImage f
    let L := (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    refine ⟨n, L, (derivedInverseImage f).mapIso e ≪≫
      P.mapDerivedCategoryFactors.app K, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact P.map_isZero (K.isZero_of_isStrictlyGE n i hi))

def Stratum.star {X : TopCat.{u}} (S : Stratum X) : Derived X ⥤ Derived S.space :=
  derivedInverseImage S.inclusion

def Stratum.shriek {X : TopCat.{u}} (S : Stratum X) : BoundedBelow X ⥤ BoundedBelow S.space :=
  boundedBelowInverseImage (openInclusion S.ambientOpen) ⋙ derivedExtraordinaryInverseImage S.closed

/-- Middle perversity uses complex dimension, with the cohomological shift convention. -/
def IsMiddlePerverse {X : TopCat.{u}} (P : Stratification X) (F : Derived X) : Prop :=
  IsConstructible P F ∧
    ∃ h : DerivedCategory.TStructure.t.plus F,
      ∀ s : P.Index,
        (∀ a : ℤ, -(P.stratum s).complexDimension < a →
          IsZero ((cohomology (P.stratum s).space a).obj ((P.stratum s).star.obj F))) ∧
        (∀ a : ℤ, a < -(P.stratum s).complexDimension →
          IsZero ((DerivedCategory.Plus.homologyFunctor _ a).obj
            ((P.stratum s).shriek.obj ⟨F, h⟩)))

abbrev MiddlePerverse {X : TopCat.{u}} (P : Stratification X) :=
  (show ObjectProperty (Derived X) from IsMiddlePerverse P).FullSubcategory

/-- An exhaustion of the union by its closed stages, with their analytic subspace topologies. -/
structure ClosedStages (X : TopCat.{u}) where
  stage : ℕ → Set X
  closed : ∀ n, IsClosed (stage n)
  monotone : Monotone stage
  exhaustive : ∀ x : X, ∃ n, x ∈ stage n

abbrev ClosedStages.space {X : TopCat.{u}} (A : ClosedStages X) (n : ℕ) : TopCat.{u} :=
  TopCat.of (A.stage n)

def ClosedStages.extension {X : TopCat.{u}} (A : ClosedStages X) (n : ℕ) :
    Derived (A.space n) ⥤ Derived X :=
  closedExtension (A.closed n)

def HasFiniteStageSupport {X : TopCat.{u}} (A : ClosedStages X) (F : Derived X) : Prop :=
  ∃ n : ℕ, (A.extension n).essImage F

def IsFiniteStagePerverse {X : TopCat.{u}} (A : ClosedStages X)
    (P : ∀ n, Stratification (A.space n)) (F : Derived X) : Prop :=
  ∃ (n : ℕ) (G : MiddlePerverse (P n)), Nonempty ((A.extension n).obj G.obj ≅ F)

abbrev FiniteStagePerverse {X : TopCat.{u}} (A : ClosedStages X)
    (P : ∀ n, Stratification (A.space n)) :=
  (show ObjectProperty (Derived X) from IsFiniteStagePerverse A P).FullSubcategory

/-- Canonical comparison of the inverse image of a composition with the successive inverse images. -/
def inverseImageComposition {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverseImage (f ≫ g) ≅ inverseImage g ⋙ inverseImage f :=
  (inverseDirectAdjunction (f ≫ g)).leftAdjointUniq
    ((inverseDirectAdjunction g).comp (inverseDirectAdjunction f))

/-- The same comparison on derived categories, obtained by localization of cochain complexes. -/
def derivedInverseImageComposition {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedInverseImage (f ≫ g) ≅ derivedInverseImage g ⋙ derivedInverseImage f := by
  let A := inverseImage (f ≫ g)
  let B := inverseImage g ⋙ inverseImage f
  have e : A.mapDerivedCategory ≅ B.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (Sheaves Z) (.up ℤ))
      (A.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (B.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      A.mapDerivedCategory B.mapDerivedCategory
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex (inverseImageComposition f g) _)
        (DerivedCategory.Q (C := Sheaves X)))
  exact e ≪≫ (Functor.mapDerivedCategoryCompIso (inverseImage g) (inverseImage f)).symm

/-- Pull back a morphism between two inverse images, using the canonical composition comparisons. -/
def pullbackMorphism {W Y X : TopCat.{u}} {f g : Y ⟶ X} {F : Derived X}
    (k : W ⟶ Y) {f' g' : W ⟶ X} (hf : k ≫ f = f') (hg : k ≫ g = g')
    (v : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F) :
    (derivedInverseImage f').obj F ⟶ (derivedInverseImage g').obj F :=
  eqToHom (congrArg (fun t => (derivedInverseImage t).obj F) hf.symm) ≫
    (derivedInverseImageComposition k f).hom.app F ≫ (derivedInverseImage k).map v ≫
    (derivedInverseImageComposition k g).inv.app F ≫
    eqToHom (congrArg (fun t => (derivedInverseImage t).obj F) hg)

/-- A topological group of analytic parameters, for example a finite jet group. -/
structure AnalyticGroup where
  space : TopCat.{u}
  [group : Group space]
  [topologicalGroup : IsTopologicalGroup space]

attribute [instance] AnalyticGroup.group AnalyticGroup.topologicalGroup

structure AnalyticAction (H : AnalyticGroup.{u}) (X : TopCat.{u}) where
  act : TopCat.of (H.space × X) ⟶ X
  one_act : ∀ x : X, act (1, x) = x
  mul_act : ∀ (h k : H.space) (x : X), act (h * k, x) = act (h, act (k, x))

namespace AnalyticAction

variable {H : AnalyticGroup.{u}} {X : TopCat.{u}}

abbrev Parameters (H : AnalyticGroup.{u}) (X : TopCat.{u}) : TopCat.{u} :=
  TopCat.of (H.space × X)

def projection (H : AnalyticGroup.{u}) (X : TopCat.{u}) : Parameters H X ⟶ X :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

def identitySection (H : AnalyticGroup.{u}) (X : TopCat.{u}) : X ⟶ Parameters H X :=
  TopCat.ofHom ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩

abbrev TwoParameters (H : AnalyticGroup.{u}) (X : TopCat.{u}) : TopCat.{u} :=
  TopCat.of (H.space × (H.space × X))

def multiplyParameters (H : AnalyticGroup.{u}) (X : TopCat.{u}) :
    TwoParameters H X ⟶ Parameters H X :=
  TopCat.ofHom ⟨fun p => (p.1 * p.2.1, p.2.2),
    (continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)⟩

def secondParameter (H : AnalyticGroup.{u}) (X : TopCat.{u}) :
    TwoParameters H X ⟶ Parameters H X :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

def firstAfterSecond (A : AnalyticAction H X) : TwoParameters H X ⟶ Parameters H X :=
  TopCat.ofHom ⟨fun p => (p.1, A.act p.2), continuous_fst.prodMk
    (A.act.hom.continuous.comp continuous_snd)⟩

theorem identity_act (A : AnalyticAction H X) : identitySection H X ≫ A.act = 𝟙 X :=
  TopCat.ext (fun x => A.one_act x)

theorem identity_projection : identitySection H X ≫ projection H X = 𝟙 X :=
  TopCat.ext (fun _ => rfl)

theorem multiply_act (A : AnalyticAction H X) :
    firstAfterSecond A ≫ A.act = multiplyParameters H X ≫ A.act :=
  TopCat.ext (fun p => (A.mul_act p.1 p.2.1 p.2.2).symm)

theorem first_projection (A : AnalyticAction H X) :
    firstAfterSecond A ≫ projection H X = secondParameter H X ≫ A.act :=
  TopCat.ext (fun _ => rfl)

theorem multiply_projection :
    secondParameter H X ≫ projection H X = multiplyParameters H X ≫ projection H X :=
  TopCat.ext (fun _ => rfl)

/-- A normalized datum on a derived sheaf satisfies the identity and multiplication equations. -/
structure Equivariance (A : AnalyticAction H X) (F : Derived X) where
  iso : (derivedInverseImage A.act).obj F ≅ (derivedInverseImage (projection H X)).obj F
  identity : pullbackMorphism (identitySection H X) (identity_act A) identity_projection iso.hom = 𝟙 _
  multiplication :
    pullbackMorphism (multiplyParameters H X) rfl rfl iso.hom =
      pullbackMorphism (firstAfterSecond A) (multiply_act A) (first_projection A) iso.hom ≫
      pullbackMorphism (secondParameter H X) rfl multiply_projection iso.hom

end AnalyticAction

/-- A common derived sheaf with its normalized equivariance. -/
structure EquivariantSheaf {H : AnalyticGroup.{u}} {X : TopCat.{u}} (A : AnalyticAction H X) where
  obj : Derived X
  equivariance : A.Equivariance obj

namespace EquivariantSheaf

variable {H : AnalyticGroup.{u}} {X : TopCat.{u}} {A : AnalyticAction H X}

@[ext]
structure Hom (F G : EquivariantSheaf A) where
  hom : F.obj ⟶ G.obj
  comm : (derivedInverseImage A.act).map hom ≫ G.equivariance.iso.hom =
    F.equivariance.iso.hom ≫ (derivedInverseImage (AnalyticAction.projection H X)).map hom

instance : Category (EquivariantSheaf A) where
  Hom := Hom
  id F := ⟨𝟙 F.obj, by simp⟩
  comp v w := ⟨v.hom ≫ w.hom, by
    simp only [Functor.map_comp, Category.assoc, w.comm, reassoc_of% v.comm]⟩
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

def forget (A : AnalyticAction H X) : EquivariantSheaf A ⥤ Derived X where
  obj := EquivariantSheaf.obj
  map v := v.hom

abbrev Perverse (A : AnalyticAction H X) (P : Stratification X) :=
  ((show ObjectProperty (Derived X) from IsMiddlePerverse P).inverseImage
    (forget A)).FullSubcategory

end EquivariantSheaf

/-- Finite positive jet groups with their actual truncation maps. -/
structure JetSystem where
  group : ℕ → AnalyticGroup.{u}
  truncate : ∀ (k l : ℕ), k ≤ l → ((group l).space ⟶ (group k).space)
  truncate_one : ∀ {k l : ℕ} (h : k ≤ l), (truncate k l h) 1 = 1
  truncate_mul : ∀ {k l : ℕ} (h : k ≤ l) (a b : (group l).space),
    (truncate k l h) (a * b) = (truncate k l h) a * (truncate k l h) b
  truncate_id : ∀ k : ℕ, truncate k k (le_refl k) = 𝟙 _
  truncate_comp : ∀ {k l m : ℕ} (h : k ≤ l) (j : l ≤ m),
    truncate l m j ≫ truncate k l h = truncate k m (h.trans j)

def JetSystem.parameterMap (J : JetSystem.{u}) {k l : ℕ} (h : k ≤ l)
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    AnalyticAction.Parameters (J.group l) X ⟶ AnalyticAction.Parameters (J.group k) Y :=
  TopCat.ofHom ⟨fun p => (J.truncate k l h p.1, f p.2),
    ((J.truncate k l h).hom.continuous.comp continuous_fst).prodMk
      (f.hom.continuous.comp continuous_snd)⟩

/-- The action on a stage is defined at some finite jet level and on all higher levels. -/
structure JetAction (J : JetSystem.{u}) (X : TopCat.{u}) where
  cutoff : ℕ
  action : ∀ k : ℕ, cutoff ≤ k → AnalyticAction (J.group k) X
  factors : ∀ {k l : ℕ} (hk : cutoff ≤ k) (h : k ≤ l),
    J.parameterMap h (𝟙 X) ≫ (action k hk).act = (action l (hk.trans h)).act

namespace JetAction

variable {J : JetSystem.{u}} {X : TopCat.{u}}

structure Equivariance (A : JetAction J X) (F : Derived X) where
  datum : ∀ (k : ℕ) (hk : A.cutoff ≤ k), (A.action k hk).Equivariance F
  compatibility : ∀ {k l : ℕ} (hk : A.cutoff ≤ k) (h : k ≤ l),
    pullbackMorphism (J.parameterMap h (𝟙 X)) (A.factors hk h)
      (TopCat.ext (fun _ => rfl)) (datum k hk).iso.hom =
        (datum l (hk.trans h)).iso.hom

structure Object (A : JetAction J X) where
  obj : Derived X
  equivariance : A.Equivariance obj

variable {A : JetAction J X}

@[ext]
structure Hom (F G : A.Object) where
  hom : F.obj ⟶ G.obj
  comm : ∀ (k : ℕ) (hk : A.cutoff ≤ k),
    (derivedInverseImage (A.action k hk).act).map hom ≫ (G.equivariance.datum k hk).iso.hom =
      (F.equivariance.datum k hk).iso.hom ≫
        (derivedInverseImage (AnalyticAction.projection (J.group k) X)).map hom

instance : Category A.Object where
  Hom := Hom
  id F := ⟨𝟙 F.obj, by simp⟩
  comp v w := ⟨v.hom ≫ w.hom, by
    intro k hk
    simp only [Functor.map_comp, Category.assoc, w.comm k hk, reassoc_of% (v.comm k hk)]⟩
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

def forget (A : JetAction J X) : A.Object ⥤ Derived X where
  obj := Object.obj
  map v := v.hom

abbrev Perverse (A : JetAction J X) (P : Stratification X) :=
  ((show ObjectProperty (Derived X) from IsMiddlePerverse P).inverseImage
    (forget A)).FullSubcategory

end JetAction

def ClosedStages.inclusion {X : TopCat.{u}} (A : ClosedStages X) (n : ℕ) : A.space n ⟶ X :=
  closedInclusion (A.stage n)

def ClosedStages.transition {X : TopCat.{u}} (A : ClosedStages X) {n m : ℕ} (h : n ≤ m) :
    A.space n ⟶ A.space m :=
  TopCat.ofHom ⟨fun x => ⟨x.val, A.monotone h x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem ClosedStages.transition_inclusion {X : TopCat.{u}} (A : ClosedStages X)
    {n m : ℕ} (h : n ≤ m) : A.transition h ≫ A.inclusion m = A.inclusion n :=
  TopCat.ext (fun _ => rfl)

/-- The finite jet actions on the union are specified on its closed stages. -/
structure StageJetActions {X : TopCat.{u}} (J : JetSystem.{u}) (A : ClosedStages X) where
  stageAction : ∀ n : ℕ, JetAction J (A.space n)
  compatible : ∀ {n m k : ℕ} (h : n ≤ m)
    (hn : (stageAction n).cutoff ≤ k) (hm : (stageAction m).cutoff ≤ k),
    J.parameterMap (le_refl k) (A.transition h) ≫ ((stageAction m).action k hm).act =
      ((stageAction n).action k hn).act ≫ A.transition h

namespace StageJetActions

variable {X : TopCat.{u}} {J : JetSystem.{u}} {A : ClosedStages X}

def restrictionComparison (F : Derived X) {n m : ℕ} (h : n ≤ m) :
    (derivedInverseImage (A.inclusion n)).obj F ≅
      (derivedInverseImage (A.transition h)).obj ((derivedInverseImage (A.inclusion m)).obj F) :=
  eqToIso (congrArg (fun t => (derivedInverseImage t).obj F)
    (A.transition_inclusion h).symm) ≪≫
      (derivedInverseImageComposition (A.transition h) (A.inclusion m)).app F

/-- Pull the equivariance arrow on a larger stage back to a smaller stage at the same jet level. -/
def restrictDatum (B : StageJetActions J A) {F : Derived X} {n m k : ℕ} (h : n ≤ m)
    (hn : (B.stageAction n).cutoff ≤ k) (hm : (B.stageAction m).cutoff ≤ k)
    (e : ((B.stageAction m).action k hm).Equivariance
      ((derivedInverseImage (A.inclusion m)).obj F)) :
    (derivedInverseImage ((B.stageAction n).action k hn).act).obj
        ((derivedInverseImage (A.inclusion n)).obj F) ⟶
      (derivedInverseImage (AnalyticAction.projection (J.group k) (A.space n))).obj
        ((derivedInverseImage (A.inclusion n)).obj F) :=
  let a := ((B.stageAction n).action k hn).act
  let p := AnalyticAction.projection (J.group k) (A.space n)
  let t := A.transition h
  let G := (derivedInverseImage (A.inclusion m)).obj F
  let c := restrictionComparison F h
  (derivedInverseImage a).map c.hom ≫ (derivedInverseImageComposition a t).inv.app G ≫
    pullbackMorphism (J.parameterMap (le_refl k) t) (B.compatible h hn hm)
      (show _ ≫ AnalyticAction.projection (J.group k) (A.space m) = p ≫ t from
        TopCat.ext (fun _ => rfl)) e.iso.hom ≫
    (derivedInverseImageComposition p t).hom.app G ≫ (derivedInverseImage p).map c.inv

/-- Equivariance on the union is given by compatible finite-jet data on all closed stages. -/
structure Equivariance (B : StageJetActions J A) (F : Derived X) where
  datum : ∀ n : ℕ, (B.stageAction n).Equivariance ((derivedInverseImage (A.inclusion n)).obj F)
  compatibility : ∀ {n m k : ℕ} (h : n ≤ m)
    (hn : (B.stageAction n).cutoff ≤ k) (hm : (B.stageAction m).cutoff ≤ k),
    B.restrictDatum h hn hm ((datum m).datum k hm) = ((datum n).datum k hn).iso.hom

structure Object (B : StageJetActions J A) where
  obj : Derived X
  equivariance : B.Equivariance obj

variable {B : StageJetActions J A}

@[ext]
structure Hom (F G : B.Object) where
  hom : F.obj ⟶ G.obj
  comm : ∀ (n k : ℕ) (hk : (B.stageAction n).cutoff ≤ k),
    (derivedInverseImage ((B.stageAction n).action k hk).act).map
        ((derivedInverseImage (A.inclusion n)).map hom) ≫ ((G.equivariance.datum n).datum k hk).iso.hom =
      ((F.equivariance.datum n).datum k hk).iso.hom ≫
        (derivedInverseImage (AnalyticAction.projection (J.group k) (A.space n))).map
          ((derivedInverseImage (A.inclusion n)).map hom)

instance : Category B.Object where
  Hom := Hom
  id F := ⟨𝟙 F.obj, by simp⟩
  comp v w := ⟨v.hom ≫ w.hom, by
    intro n k hk
    simp only [Functor.map_comp, Category.assoc, w.comm n k hk, reassoc_of% (v.comm n k hk)]⟩
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

def forget (B : StageJetActions J A) : B.Object ⥤ Derived X where
  obj := Object.obj
  map v := v.hom

abbrev FiniteSupportPerverse (B : StageJetActions J A)
    (P : ∀ n, Stratification (A.space n)) :=
  ((show ObjectProperty (Derived X) from IsFiniteStagePerverse A P).inverseImage
    (forget B)).FullSubcategory

end StageJetActions

/-- Evaluation on an open subset, with the restrictions of the underlying presheaf. -/
abbrev sectionsOn {X : TopCat.{u}} (U : Opens X) : Sheaves X ⥤ Coeff.{u} :=
  TopCat.Sheaf.forget _ X ⋙ (evaluation _ _).obj (op U)

instance {X : TopCat.{u}} (U : Opens X) : (sectionsOn U).Additive where
  map_add := by intros; rfl

instance {X : TopCat.{u}} (U : Opens X) : PreservesFiniteLimits (sectionsOn U) := by
  change PreservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) Coeff.{u} ⋙
      (evaluation (Opens X)ᵒᵖ Coeff.{u}).obj (op U))
  exact comp_preservesFiniteLimits _ _

namespace Expected

def SheavesType := TopCat.{u} → Type (u + 1)

def DerivedType := TopCat.{u} → Type (u + 1)

def BoundedBelowType := TopCat.{u} → Type (u + 1)

def ConstantType := ∀ (X : TopCat.{u}), Coeff.{u} → Sheaves X

def RationalType := ∀ (X : TopCat.{u}), Sheaves X

def StalkType := ∀ {X : TopCat.{u}}, X → (Sheaves X ⥤ Coeff.{u})

def InverseImageType := ∀ {X Y : TopCat.{u}}, (X ⟶ Y) → (Sheaves Y ⥤ Sheaves X)

def DirectImageType := ∀ {X Y : TopCat.{u}}, (X ⟶ Y) → (Sheaves X ⥤ Sheaves Y)

def InverseDirectAdjunctionType := ∀ {X Y : TopCat.{u}} (f : X ⟶ Y), inverseImage f ⊣ directImage f

def DerivedInverseImageType := ∀ {X Y : TopCat.{u}}, (X ⟶ Y) → (Derived Y ⥤ Derived X)

def DerivedDirectImageType := ∀ {X Y : TopCat.{u}}, (X ⟶ Y) → (BoundedBelow X ⥤ BoundedBelow Y)

def BoundedBelowInverseImageType := ∀ {X Y : TopCat.{u}}, (X ⟶ Y) → (BoundedBelow Y ⥤ BoundedBelow X)

def CohomologyType := ∀ (X : TopCat.{u}), ℤ → (Derived X ⥤ Sheaves X)

def ShiftCohomologyType := ∀ (X : TopCat.{u}) (a b : ℤ),
    shiftFunctor (Derived X) b ⋙ cohomology X a ≅ cohomology X (a + b)

def SectionsWithSupportType := ∀ {X : TopCat.{u}} {Z : Set X}, IsClosed Z → (Sheaves X ⥤ Sheaves X)

def ExtraordinaryInverseImageType := ∀ {X : TopCat.{u}} {Z : Set X},
    IsClosed Z → (Sheaves X ⥤ Sheaves (TopCat.of Z))

def ExtraordinaryAdjunctionType := ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z),
    directImage (closedInclusion Z) ⊣ extraordinaryInverseImage hZ

def DerivedExtraordinaryInverseImageType := ∀ {X : TopCat.{u}} {Z : Set X},
    IsClosed Z → (BoundedBelow X ⥤ BoundedBelow (TopCat.of Z))

def ClosedExtensionType := ∀ {X : TopCat.{u}} {Z : Set X}, IsClosed Z → (Derived (TopCat.of Z) ⥤ Derived X)

def StratumStarType := ∀ {X : TopCat.{u}} (S : Stratum X), Derived X ⥤ Derived S.space

def StratumShriekType := ∀ {X : TopCat.{u}} (S : Stratum X), BoundedBelow X ⥤ BoundedBelow S.space

def ConstructibleType := ∀ {X : TopCat.{u}}, Stratification X → Type (u + 1)

def MiddlePerverseType := ∀ {X : TopCat.{u}}, Stratification X → Type (u + 1)

def FiniteStagePerverseType := ∀ {X : TopCat.{u}} (A : ClosedStages X),
    (∀ n, Stratification (A.space n)) → Type (u + 1)

def EquivarianceType := ∀ {H : AnalyticGroup.{u}} {X : TopCat.{u}},
    AnalyticAction H X → Derived X → Type (u + 1)

abbrev equivarianceModel : EquivarianceType.{u} := @AnalyticAction.Equivariance.{u}

def EquivariantPerverseType := ∀ {H : AnalyticGroup.{u}} {X : TopCat.{u}},
    AnalyticAction H X → Stratification X → Type (u + 1)

def JetEquivariantPerverseType := ∀ {J : JetSystem.{u}} {X : TopCat.{u}},
    JetAction J X → Stratification X → Type (u + 1)

def JetEquivariantFiniteSupportPerverseType := ∀ {X : TopCat.{u}} {J : JetSystem.{u}} {A : ClosedStages X},
    StageJetActions J A → (∀ n, Stratification (A.space n)) → Type (u + 1)

def StalkExact : Prop :=
  ∀ {X : TopCat.{u}} (x : X) (S : ShortComplex (Sheaves X)), S.Exact → (S.map (stalk x)).Exact

def SupportedEssentialImage : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X}, IsClosed Z → ∀ F : Sheaves X,
    (directImage (closedInclusion Z)).essImage F ↔ SupportedOn Z F

def ConstructibleBounded : Prop :=
  ∀ {X : TopCat.{u}} (P : Stratification X) (F : Derived X), IsConstructible P F →
    DerivedCategory.TStructure.t.bounded F

def SupportSectionsKernel : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X) (F : Sheaves X),
    let r := F.obj.map (homOfLE (inf_le_left : U ⊓ complementOpen Z hZ ≤ U)).op
    ∃ e : (sectionsOn U).obj ((sectionsWithSupport hZ).obj F) ≅ kernel r,
      e.hom ≫ kernel.ι r = (sectionsOn U).map ((sectionsWithSupportInclusion hZ).app F)

end Expected

end RepTheorySurvey.Geometric.Analytic
