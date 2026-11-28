import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Topology.Sheaves.Flasque

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite TopologicalSpace Topology

universe u

namespace RepTheorySurvey.Geometric.LocalSheaf

open Analytic

/-- The complex underlying a bounded-below complex of injective objects. -/
abbrev injectiveComplex {C : Type*} [Category* C] [Abelian C]
    (I : CochainComplex.Plus (InjectiveObject C)) : CochainComplex.Plus C :=
  (InjectiveObject.ι C).mapCochainComplexPlus.obj I

/-- Open sections of a cochain complex, with restriction as transition maps. -/
def openSectionComplexes {X : TopCat.{u}} (K : CochainComplex (Sheaves X) ℤ) :
    (Opens X)ᵒᵖ ⥤ CochainComplex Coeff.{u} ℤ :=
  ((TopCat.Sheaf.forget Coeff.{u} X).mapHomologicalComplex (.up ℤ)).obj K |>.asFunctor

/-- Cohomology of open sections of the complex, with transition maps on cohomology. -/
def openSectionCohomology {X : TopCat.{u}} (K : CochainComplex (Sheaves X) ℤ) (q : ℤ) :
    X.Presheaf Coeff.{u} :=
  openSectionComplexes K ⋙ HomologicalComplex.homologyFunctor _ _ q

/-- Cohomology of sections on the inverse images of opens under a continuous map. -/
def directImageCohomology {Y X : TopCat.{u}} (m : Y ⟶ X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaves Y))) (q : ℤ) :
    X.Presheaf Coeff.{u} :=
  openSectionCohomology (((directImage m).mapCochainComplexPlus.obj (injectiveComplex I)).obj) q

/-- Cohomology of sections vanishing outside the closed set, on each open. -/
def supportCohomology {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (I : CochainComplex.Plus (InjectiveObject (Sheaves X))) (q : ℤ) :
    X.Presheaf Coeff.{u} :=
  openSectionCohomology
    ((((extraordinaryInverseImage hZ ⋙ directImage (closedInclusion Z)).mapCochainComplexPlus).obj
      (injectiveComplex I)).obj) q

abbrev stalkColimit {X : TopCat.{u}} (P : X.Presheaf Coeff.{u}) (x : X) : Coeff.{u} :=
  colimit ((OpenNhds.inclusion x).op ⋙ P)

/-- Restriction of the functor on the ordinary derived category to bounded-below objects. -/
def exactDerivedPlus {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  DerivedCategory.TStructure.t.plus.lift
    (DerivedCategory.Plus.ι ⋙ L.mapDerivedCategory) (by
      rintro ⟨F, n, K, e, hK⟩
      let M := (L.mapHomologicalComplex (.up ℤ)).obj K
      refine ⟨n, M, L.mapDerivedCategory.mapIso e ≪≫ L.mapDerivedCategoryFactors.app K, ?_⟩
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact L.map_isZero (K.isZero_of_isStrictlyGE n i hi))

/-- The bounded-below form of the shared exact closed extension. -/
def closedExtensionPlus {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    BoundedBelow (TopCat.of Z) ⥤ BoundedBelow X := by
  letI := (extraordinaryAdjunction hZ).isLeftAdjoint
  exact exactDerivedPlus (directImage (closedInclusion Z))

instance : HasDerivedCategory.{u + 1} Coeff.{u} := HasDerivedCategory.standard _

/-- The complex of a sheaf placed in cohomological degree zero. -/
abbrev sheafInDegreeZero {X : TopCat.{u}} (F : Sheaves X) : BoundedBelow X :=
  (DerivedCategory.Plus.singleFunctor (Sheaves X) 0).obj F

/-- The inclusion of the sections vanishing away from a closed subset. -/
def supportedImageIso {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    sectionsWithSupport hZ ≅ extraordinaryInverseImage hZ ⋙ directImage (closedInclusion Z) := by
  let i := closedInclusion Z
  let a := inverseDirectAdjunction i
  letI (F : Sheaves X) : IsIso (a.unit.app ((sectionsWithSupport hZ).obj F)) :=
    closedInverseDirectUnit_isIso hZ _ (sectionsWithSupport_supported hZ F)
  exact NatIso.ofComponents (fun F => asIso (a.unit.app ((sectionsWithSupport hZ).obj F)))
    (fun f => a.unit.naturality ((sectionsWithSupport hZ).map f))

/-- Sections over an open with support in its intersection with the closed set. -/
def supportedSectionsOn {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X) :
    Sheaves X ⥤ Coeff.{u} :=
  (extraordinaryInverseImage hZ ⋙ directImage (closedInclusion Z)) ⋙ sectionsOn U

instance {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X) :
    (supportedSectionsOn hZ U).Additive := by
  unfold supportedSectionsOn
  infer_instance

/-- The natural inclusion from supported sections to all sections. -/
def supportedSectionsInclusion {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X) :
    supportedSectionsOn hZ U ⟶ sectionsOn U :=
  Functor.whiskerRight ((supportedImageIso hZ).inv ≫ sectionsWithSupportInclusion hZ) _
    ≫ (sectionsOn U).leftUnitor.hom

/-- Restriction of sections along an inclusion of opens. -/
abbrev sectionsRestriction {X : TopCat.{u}} {U V : Opens X} (i : U ⟶ V) :
    sectionsOn V ⟶ sectionsOn U :=
  Functor.whiskerLeft (TopCat.Sheaf.forget Coeff.{u} X)
    ((evaluation (Opens X)ᵒᵖ Coeff.{u}).map i.op)

/-- Restriction from an open to the complement of the closed set within it. -/
abbrev restrictionOffClosed {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X) :
    sectionsOn U ⟶ sectionsOn (U ⊓ complementOpen Z hZ) :=
  sectionsRestriction (homOfLE inf_le_left)

/-- The derived cohomology presheaf for sections of a given additive sheaf functor.
The maps are obtained by deriving the actual restriction transformations. -/
def derivedOpenCohomology {X : TopCat.{u}} (T : Sheaves X ⥤ Sheaves X) [T.Additive]
    (F : BoundedBelow X) (q : ℤ) : X.Presheaf Coeff.{u} where
  obj U := (DerivedCategory.Plus.homologyFunctor _ q).obj
    ((T ⋙ sectionsOn U.unop).rightDerivedFunctorPlus.obj F)
  map i := (DerivedCategory.Plus.homologyFunctor _ q).map
    ((Functor.whiskerLeft T (sectionsRestriction i.unop)).rightDerivedFunctorPlus.app F)
  map_id U := by
    simp [sectionsRestriction]
  map_comp i j := by
    have h : Functor.whiskerLeft T (sectionsRestriction (i ≫ j).unop) =
        Functor.whiskerLeft T (sectionsRestriction i.unop) ≫
          Functor.whiskerLeft T (sectionsRestriction j.unop) := by
      ext1
      funext E
      exact (T.obj E).obj.map_comp i j
    rw [h, NatTrans.rightDerivedFunctorPlus_comp]
    exact Functor.map_comp _ _ _

def globalSections (Y : TopCat.{u}) : Sheaves Y ⥤ Coeff.{u} :=
  sectionsOn (X := Y) (⊤ : Opens Y)

instance (Y : TopCat.{u}) : (globalSections Y).Additive where
  map_add := by intros; rfl

/-- The subset of the open subspace cut out by the given closed subset. -/
abbrev closedSetOnOpen {X : TopCat.{u}} (U : Opens X) (Z : Set X) : Set U :=
  Subtype.val ⁻¹' Z

theorem closedSetOnOpen_isClosed {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X) :
    IsClosed (closedSetOnOpen U Z) :=
  hZ.preimage continuous_subtype_val

/-- The full collection of cohomology sheaves of a complex is supported on a closed subset. -/
def DerivedSupportedOn {X : TopCat.{u}} (Z : Set X) (F : BoundedBelow X) : Prop :=
  ∀ q : ℤ, SupportedOn Z ((DerivedCategory.Plus.homologyFunctor _ q).obj F)

namespace Expected

def DerivedExtraordinaryAdjunction : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z),
    Nonempty (closedExtensionPlus hZ ⊣ derivedExtraordinaryInverseImage hZ)


def RestrictionPreservesInjectives : Prop :=
  ∀ {X : TopCat.{u}} (U : Opens X) (F : Sheaves X), Injective F →
    Injective ((inverseImage (openInclusion U)).obj F)

def InverseImageExact : Prop :=
  ∀ {X Y : TopCat.{u}} (m : Y ⟶ X) (S : ShortComplex (Sheaves X)),
    S.ShortExact → (S.map (inverseImage m)).ShortExact

def ClosedDirectImageExact : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (_ : IsClosed Z) (S : ShortComplex (Sheaves (TopCat.of Z))),
    S.ShortExact → (S.map (directImage (closedInclusion Z))).ShortExact

def ClosedDirectImageFullyFaithful :=
  ∀ {X : TopCat.{u}} (Z : Set X), (directImage (closedInclusion Z)).FullyFaithful

def SupportedEssentialImage : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X}, IsClosed Z → ∀ F : Sheaves X,
    (directImage (closedInclusion Z)).essImage F ↔ SupportedOn Z F

def DirectImageStalk : Prop :=
  ∀ {Y X : TopCat.{u}} (m : Y ⟶ X) (x : X) (q : ℤ) (F : BoundedBelow Y)
    (I : CochainComplex.Plus (InjectiveObject (Sheaves Y))),
    (DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) →
    Nonempty (((DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk x).obj
      ((derivedDirectImage m).obj F)) ≅ stalkColimit (directImageCohomology m I q) x)

def ExtraordinaryInverseImageStalk : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (x : Z) (q : ℤ)
    (F : BoundedBelow X) (I : CochainComplex.Plus (InjectiveObject (Sheaves X))),
    (DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) →
    Nonempty (((DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk x).obj
      ((derivedExtraordinaryInverseImage hZ).obj F)) ≅ stalkColimit (supportCohomology hZ I q) x.val)

def StalkExact : Prop :=
  ∀ {X : TopCat.{u}} (x : X) (S : ShortComplex (Sheaves X)),
    S.ShortExact → (S.map (stalk x)).ShortExact

def ClosedDirectImageFullyFaithfulValue : ClosedDirectImageFullyFaithful.{u} :=
  fun Z => Analytic.closedDirectImageFullyFaithful Z

def DerivedClosedExtensionFullyFaithful : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z), Nonempty (closedExtensionPlus hZ).FullyFaithful

def DerivedSupportedEssentialImage : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (F : BoundedBelow X),
    (closedExtensionPlus hZ).essImage F ↔ DerivedSupportedOn Z F

def OpenSectionsLocality : Prop :=
  ∀ {X : TopCat.{u}} (U : Opens X),
    Nonempty ((sectionsOn U).rightDerivedFunctorPlus ≅
      boundedBelowInverseImage (openInclusion U) ⋙ (globalSections (TopCat.of U)).rightDerivedFunctorPlus)

def ConstantOpenRestriction : Prop :=
  ∀ {X : TopCat.{u}} (U : Opens X),
    Nonempty ((inverseImage (openInclusion U)).obj (rational X) ≅ rational (TopCat.of U))

def SupportedSectionsLocality : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X),
    Nonempty ((supportedSectionsOn hZ U).rightDerivedFunctorPlus ≅
      boundedBelowInverseImage (openInclusion U) ⋙
        (supportedSectionsOn (X := TopCat.of U) (Z := closedSetOnOpen U Z)
          (closedSetOnOpen_isClosed hZ U) ⊤).rightDerivedFunctorPlus)

def DirectImageCohomologyRestriction : Prop :=
  ∀ {Y X : TopCat.{u}} (m : Y ⟶ X) (q : ℤ) (F : BoundedBelow Y)
    (I : CochainComplex.Plus (InjectiveObject (Sheaves Y))),
    (DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) →
    Nonempty (directImageCohomology m I q ≅
      (Opens.map m).op ⋙ derivedOpenCohomology (𝟭 (Sheaves Y)) F q)

def SupportCohomologyRestriction : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (q : ℤ) (F : BoundedBelow X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaves X))),
    (DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) →
    Nonempty (supportCohomology hZ I q ≅
      derivedOpenCohomology (extraordinaryInverseImage hZ ⋙ directImage (closedInclusion Z)) F q)

/-- The neighborhood formula with the right-hand side defined by derived sections. -/
def HigherDirectImageStalk : Prop :=
  ∀ {Y X : TopCat.{u}} (m : Y ⟶ X) (x : X) (q : ℤ) (F : BoundedBelow Y),
    Nonempty (((DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk x).obj
      ((derivedDirectImage m).obj F)) ≅
      stalkColimit ((Opens.map m).op ⋙ derivedOpenCohomology (𝟭 (Sheaves Y)) F q) x)

/-- The corresponding neighborhood formula for the derived extraordinary inverse image. -/
def Costalk : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (x : Z) (q : ℤ) (F : BoundedBelow X),
    Nonempty (((DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk x).obj
      ((derivedExtraordinaryInverseImage hZ).obj F)) ≅
      stalkColimit (derivedOpenCohomology
        (extraordinaryInverseImage hZ ⋙ directImage (closedInclusion Z)) F q) x.val)

def SupportedSectionsRestrictionTriangle : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X) (F : BoundedBelow X),
    let L := DerivedCategory.Plus.ι (C := Coeff.{u})
    let a := (supportedSectionsInclusion hZ U).rightDerivedFunctorPlus.app F
    let b := (restrictionOffClosed hZ U).rightDerivedFunctorPlus.app F
    ∃ δ : L.obj ((sectionsOn (U ⊓ complementOpen Z hZ)).rightDerivedFunctorPlus.obj F) ⟶
        (L.obj ((supportedSectionsOn hZ U).rightDerivedFunctorPlus.obj F))⟦(1 : ℤ)⟧,
      Triangle.mk (L.map a) (L.map b) δ ∈ distTriang (DerivedCategory Coeff.{u})

def SupportedSectionsFlasqueResolution : Prop :=
  ∀ {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X)
    (K : CochainComplex.Plus (Sheaves X)),
    (∀ n : ℤ, TopCat.Sheaf.IsFlasque (K.obj.X n)) →
    (let S := supportedSectionsOn hZ U
     let a := ((supportedSectionsInclusion hZ U).mapCochainComplexPlus.app K).hom
     let b := ((restrictionOffClosed hZ U).mapCochainComplexPlus.app K).hom
     (∃ e : (S.mapCochainComplexPlus.obj K).obj ≅ kernel b, e.hom ≫ kernel.ι b = a) ∧
      Epi b ∧ IsIso (S.rightDerivedFunctorPlusUnit.app K) ∧
        IsIso ((sectionsOn U).rightDerivedFunctorPlusUnit.app K) ∧
        IsIso ((sectionsOn (U ⊓ complementOpen Z hZ)).rightDerivedFunctorPlusUnit.app K))

end Expected
end RepTheorySurvey.Geometric.LocalSheaf
