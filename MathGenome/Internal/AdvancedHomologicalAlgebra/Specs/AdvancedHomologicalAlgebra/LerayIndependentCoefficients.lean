import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LerayAndDegenerations
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients

/-! The global part of HA-H07 on independent original sites, rings, and
coefficient carriers. A page index of zero denotes E₂. -/
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
open TopologicalSpace Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.style.haveILetI false
set_option quotPrecheck false
set_option maxHeartbeats 1000000

namespace AdvancedHomologicalAlgebra.LerayIndependentCoefficients

open SheafTheory HigherDirectImageLocalTheory HigherDirectImagesOriginalTheory OriginalDerivedSectionsTheory
open DerivedSectionsTheory SheafUniverseTransport LerayAndDegenerations
open GrothendieckSpectralSequence GrothendieckEdges HypercohomologyDerivedNaturality
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients

universe a m u v r s

attribute [local instance] HasDerivedCategory.standard

section Diagram

variable {C C' : Type*} [Category* C] [Category* C'] [Abelian C] [Abelian C']
    (E : C ⥤ C') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- Change coefficients on the complete diagram by an exact functor. -/
def changeCoefficientsObj (X : RowDiagram C) : RowDiagram C' where
  page r p n := E.obj (X.page r p n)
  differential r p n := E.map (X.differential r p n)
  square_zero r p n := by rw [← E.map_comp, X.square_zero, E.map_zero]
  nextIso r p n := E.mapIso (X.nextIso r p n) ≪≫
    ((RowDiagram.pageComplex X r p n).mapHomologyIso E).symm
  target n := E.obj (X.target n)
  step p n := E.obj (X.step p n)
  inclusion p n := E.map (X.inclusion p n)
  down p n := E.map (X.down p n)

def changeCoefficients : RowDiagram C ⥤ RowDiagram C' where
  obj := changeCoefficientsObj E
  map {X Y} k :=
    { page := fun r p n ↦ E.map (k.page r p n)
      target := fun n ↦ E.map (k.target n)
      step := fun p n ↦ E.map (k.step p n)
      differential_comm := by
        intros; dsimp only [changeCoefficientsObj]
        rw [← E.map_comp, k.differential_comm, E.map_comp]
      next_comm := by
        intro r p n
        let g := RowDiagram.pageComplexMap k.page k.differential_comm r p n
        change E.map (k.page _ _ _) ≫ E.map (Y.nextIso r p n).hom ≫
          ((RowDiagram.pageComplex Y r p n).mapHomologyIso E).inv =
          (E.map (X.nextIso r p n).hom ≫ ((RowDiagram.pageComplex X r p n).mapHomologyIso E).inv) ≫
            ShortComplex.homologyMap (E.mapShortComplex.map g)
        rw [← E.map_comp_assoc, k.next_comm, E.map_comp, assoc,
          ShortComplex.mapHomologyIso_inv_naturality, assoc]
      inclusion_comm := by
        intros; dsimp only [changeCoefficientsObj]
        rw [← E.map_comp, k.inclusion_comm, E.map_comp]
      down_comm := by
        intros; dsimp only [changeCoefficientsObj]
        rw [← E.map_comp, k.down_comm, E.map_comp] }
  map_id X := by apply RowDiagram.Hom.ext <;> funext <;> apply E.map_id
  map_comp k l := by apply RowDiagram.Hom.ext <;> funext <;> apply E.map_comp

/-- Exact scalar change carries the quotient of consecutive filtration steps
by the canonical comparison of cokernels. -/
def changeGradedIso (X : RowDiagram C) (k : ℕ) (p n : ℤ)
    (i : X.page k p n ≅ cokernel (X.down p n)) :
    (changeCoefficientsObj E X).page k p n ≅ cokernel ((changeCoefficientsObj E X).down p n) :=
  E.mapIso i ≪≫ PreservesCokernel.iso E (X.down p n)

/-- The inclusions and transition maps present the filtration. The cokernel
of each transition is its associated graded object. -/
structure FilteredAbutment (X : RowDiagram C) : Prop where
  mono : ∀ p n, Mono (X.inclusion p n)
  down_inclusion : ∀ p n, X.down p n ≫ X.inclusion p n = X.inclusion (p+1) n
  converges : Converges X

end Diagram

/-- The change of sites on a degree-zero complex is the localization of
the termwise comparison. -/
def stalkCoordinates {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (J : A ⥤ B) [J.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J] (d : ExactDescent J) :
    J ⋙ DerivedCategory.Plus.singleFunctor B 0 ≅
      DerivedCategory.Plus.singleFunctor A 0 ⋙ d.functor :=
  mappedStalkIso J ≪≫ isoWhiskerLeft (stalkComplex A) d.factors.symm

/-- Place a coefficient object in degree zero before lifting its carrier. -/
def degreeZeroComplex (A : Type*) [Category* A] [Preadditive A] [HasZeroObject A] :
    A ⥤ CochainComplex.Plus A :=
  (CochainComplex.plus A).lift (CochainComplex.singleFunctor A 0)
    (fun _ ↦ ⟨0, inferInstance⟩)

variable {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S)

set_option hygiene false in
local notation "AX" => AmbientSheaves.{max a m v s} R
set_option hygiene false in
local notation "AY" => AmbientSheaves.{max a m u r} S
set_option hygiene false in
local notation "CX" => SectionModules.{max a m v s} R ⊤
set_option hygiene false in
local notation "CY" => SectionModules.{max a m u r} S ⊤
set_option hygiene false in
local notation "R'" => liftedRing.{max a m v s} R
set_option hygiene false in
local notation "S'" => liftedRing.{max a m u r} S
set_option hygiene false in
local notation "CY'" => ModuleCat.{max a m u v r s} (sectionRing S' ⊤)
set_option hygiene false in
local notation "D" => ambientDirectImage.{max a m} f
set_option hygiene false in
local notation "D'" => transportedDirectImage.{max a m} f
set_option hygiene false in
local notation "GX" => sectionsValue.{max a m v s} R (⊤ : Opens X)
set_option hygiene false in
local notation "GY" => sectionsValue.{max a m u r} S (⊤ : Opens Y)
set_option hygiene false in
local notation "GY'" => DerivedSectionsTheory.globalSections S'
set_option hygiene false in
local notation "T" => OriginalDerivedSectionsTheory.scalarRestriction.{max a m} f
set_option hygiene false in
local notation "JX" => transport.{max a m v s} R
set_option hygiene false in
local notation "JY" => transport.{max a m u r} S
set_option hygiene false in
local notation "LY" => ModuleCat.restrictScalars.{max a m u v r s}
  (sectionRingEquiv.{max a m u r} S (⊤ : Opens (liftedSpace.{max a m u v r s} Y))).symm.toRingHom
set_option hygiene false in
local notation "LiftX" => liftSheafCoefficients.{max a u v r s,u,r,m} R
set_option hygiene false in
local notation "LiftY" => liftSheafCoefficients.{max a u v r s,v,s,m} S
set_option hygiene false in
local notation "FM" => transportedMap.{max a m} f
set_option hygiene false in
local notation "FS" => transportedScalars.{max a m} f

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a m u v r s}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a m u v r s}]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a m u v r s}]
    [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a m u v r s}]
    [EnoughInjectives AX] [EnoughInjectives AY]
    [(JX).IsEquivalence] [(JY).IsEquivalence]

/-- The scalar equivalence is induced by the actual section-ring equivalence. -/
def targetScalarEquivalence : CY ≌ CY' :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{s,max a m u v r s,max a m u v r s}
    (sectionRingEquiv.{max a m u r} S (⊤ : Opens (liftedSpace.{max a m u v r s} Y)))).symm

/-- Return to the original global scalar action by restriction. -/
abbrev originalScalarsFunctor : CY' ⥤ CY :=
  originalScalars.{max a m u r} S (⊤ : Opens (liftedSpace.{max a m u v r s} Y))

set_option hygiene false in
local notation "B" => originalScalarsFunctor.{a,m,u,v,r,s} (S := S)

abbrev liftedLeray := LerayData R' S' FM FS

abbrev derivedSecondValue (p : ℕ) (q : ℤ) : DerivedCategory.Plus AX ⥤ CY :=
  (D).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor AY q ⋙
    cohomologyValue.{max a m u r} S ⊤ p

abbrev derivedTargetValue (n : ℤ) : DerivedCategory.Plus AX ⥤ CY :=
  (GX).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor CX n ⋙ T

abbrev sheafSecondValue (p q : ℕ) : SheafOfModules.{m} R ⥤ CY :=
  originalHigherValue.{a,m} f q ⋙ cohomologyValue.{max a m u r} S ⊤ p

abbrev sheafTargetValue (n : ℕ) : SheafOfModules.{m} R ⥤ CY :=
  LiftX ⋙ cohomologyValue.{max a m v s} R ⊤ n ⋙ T

abbrev rowValue (n : ℕ) : SheafOfModules.{m} R ⥤ CY :=
  directImageValue.{m} f ⋙ LiftY ⋙ cohomologyValue.{max a m u r} S ⊤ n

abbrev columnValue (n : ℕ) : SheafOfModules.{m} R ⥤ CY :=
  originalHigherValue.{a,m} f n ⋙ GY

abbrev originalComplexImage :
    CochainComplex.Plus (SheafOfModules.{m} R) ⥤ DerivedCategory.Plus AX :=
  (LiftX).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q

abbrev sheafInput : SheafOfModules.{m} R ⥤ Modules R' := LiftX ⋙ JX

variable {c : SectionsData.{max a m} f} {c' : liftedSectionsData.{max a m} f}

/-- The two squares for the constituents of the second page, normalized by
the actual pushforward and sections maps on injective models. Their source
site and target scalars are the ones in the abutment comparison. -/
structure PageTransport (d : SiteTransportData.{max a m} f c c') where
  targetSite : ExactDescent JY
  pushforward : ModelTransport D D' JX JY (pushforwardTransportExpected.{max a m,u,v,r,s} f)
    d.site targetSite (D).rightDerivedFunctorPlusUnit (D').rightDerivedFunctorPlusUnit
  sections : ModelTransport GY GY' JY LY (targetSectionsSquare.{max a m} f)
    targetSite d.scalars (GY).rightDerivedFunctorPlusUnit (GY').rightDerivedFunctorPlusUnit

def derivedSequence (L : liftedLeray.{a,m} f)
    (d : SiteTransportData.{max a m} f c L.sections) :
    DerivedCategory.Plus AX ⥤ RowDiagram CY :=
  d.site.functor ⋙ sequence D' GY' L.package.row ⋙ changeCoefficients B

def sheafSequence (L : liftedLeray.{a,m} f) : SheafOfModules.{m} R ⥤ RowDiagram CY :=
  sheafInput.{a,m,u,v,r,s} (R := R) ⋙ objectSequence D' GY' L.package ⋙ changeCoefficients B

/-- Recover original coordinates from the scalar equivalence. -/
def lowerCoordinates {A : Type*} [Category* A] {F : A ⥤ CY} {G : A ⥤ CY'}
    (e : F ⋙ LY ≅ G) : G ⋙ B ≅ F :=
  NatIso.ofComponents (fun K ↦ (B).mapIso (e.app K).symm ≪≫
      (targetScalarEquivalence.{a,m,u,v,r,s} (S := S)).unitIso.symm.app (F.obj K)) (by
    intro K K' k
    change (B).map (G.map k) ≫
        (B).map (e.inv.app K') ≫ (targetScalarEquivalence.{a,m,u,v,r,s} (S := S)).unitIso.inv.app (F.obj K') =
      ((B).map (e.inv.app K) ≫ (targetScalarEquivalence.{a,m,u,v,r,s} (S := S)).unitIso.inv.app (F.obj K)) ≫ F.map k
    rw [← (B).map_comp_assoc, e.inv.naturality, Functor.comp_map, (B).map_comp,
      assoc, assoc]
    congr 1)

variable {d : SiteTransportData.{max a m} f c c'}

/-- The derived higher image comparison in degree q. -/
def higherCoordinates (h : PageTransport.{a,m} f d) (q : ℤ) :
    ((D).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor AY q) ⋙ JY ≅
      d.site.functor ⋙ (D').rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor _ q :=
  associator .. ≪≫ h.pushforward.cohomology D D' JX JY q

/-- Cohomology of the actual global-sections comparison on stalk complexes. -/
def sectionsCoordinates (h : PageTransport.{a,m} f d) (p : ℕ) :
    cohomologyValue.{max a m u r} S ⊤ p ⋙ LY ≅ JY ⋙ sectionCohomology S' ⊤ p := by
  let s := DerivedCategory.Plus.singleFunctor AY 0
  let e := h.sections.cohomology GY GY' JY LY (p : ℤ)
  exact associator s _ _ ≪≫ isoWhiskerLeft s (associator .. ≪≫ e) ≪≫
    (associator s _ _).symm ≪≫
    isoWhiskerRight (stalkCoordinates JY h.targetSite).symm _ ≪≫ associator _ _ _

def derivedPageCoordinates (h : PageTransport.{a,m} f d) (p : ℕ) (q : ℤ) :
    derivedSecondValue.{a,m} f p q ⋙ LY ≅ d.site.functor ⋙ secondValue D' GY' p q :=
  (isoWhiskerRight (associator _ _ _).symm LY) ≪≫
    composeFunctorSquares (higherCoordinates.{a,m} f h q) (sectionsCoordinates.{a,m} f h p) ≪≫
    isoWhiskerLeft _ (associator _ _ _)

def sheafStalkCoordinate (d : SiteTransportData.{max a m} f c c') :
    (LiftX ⋙ DerivedCategory.Plus.singleFunctor AX 0) ⋙ d.site.functor ≅
      sheafInput.{a,m,u,v,r,s} (R := R) ⋙ DerivedCategory.Plus.singleFunctor (Modules R') 0 :=
  associator _ _ _ ≪≫ isoWhiskerLeft LiftX (stalkCoordinates JX d.site).symm ≪≫ (associator _ _ _).symm

def sheafHigherCoordinates (h : PageTransport.{a,m} f d) (q : ℕ) :
    originalHigherValue.{a,m} f q ⋙ JY ≅
      sheafInput.{a,m,u,v,r,s} (R := R) ⋙ higherDirectImage R' S' FM FS q :=
  let I := LiftX ⋙ DerivedCategory.Plus.singleFunctor AX 0
  let H := (D').rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor _ (q : ℤ)
  (show originalHigherValue.{a,m} f q ⋙ JY ≅
      I ⋙ (((D).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor AY (q : ℤ)) ⋙ JY)
    from Iso.refl _) ≪≫
    isoWhiskerLeft I (higherCoordinates.{a,m} f h (q : ℤ)) ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight (sheafStalkCoordinate.{a,m} f d) H ≪≫
    associator ..

def sheafPageCoordinates (h : PageTransport.{a,m} f d) (p q : ℕ) :
    sheafSecondValue.{a,m} f p q ⋙ LY ≅ sheafInput.{a,m,u,v,r,s} (R := R) ⋙
      (higherDirectImage R' S' FM FS q ⋙ sectionCohomology S' ⊤ p) := by
  let I := LiftX ⋙ DerivedCategory.Plus.singleFunctor AX 0
  let H := secondValue D' GY' p (q : ℤ)
  change I ⋙ (derivedSecondValue.{a,m} f p (q : ℤ) ⋙ LY) ≅
    (sheafInput.{a,m,u,v,r,s} (R := R) ⋙ DerivedCategory.Plus.singleFunctor (Modules R') 0) ⋙ H
  exact isoWhiskerLeft I (derivedPageCoordinates.{a,m} f h p (q : ℤ)) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight (sheafStalkCoordinate.{a,m} f d) H

def rowCoordinates (h : PageTransport.{a,m} f d) (n : ℕ) :
    rowValue.{a,m} f n ⋙ LY ≅ sheafInput.{a,m,u,v,r,s} (R := R) ⋙ D' ⋙
      sectionCohomology S' ⊤ n :=
  isoWhiskerRight (associator _ _ _).symm LY ≪≫
    composeFunctorSquares (isoWhiskerRight
      (coefficientLiftComparisonExpected.{max a u v r s,m,u,v,r,s} f) JY ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft LiftX (pushforwardTransportExpected.{max a m,u,v,r,s} f) ≪≫
      (associator _ _ _).symm)
      (sectionsCoordinates.{a,m} f h n)

def columnCoordinates (h : PageTransport.{a,m} f d) (n : ℕ) :
    columnValue.{a,m} f n ⋙ LY ≅ sheafInput.{a,m,u,v,r,s} (R := R) ⋙
      higherDirectImage R' S' FM FS n ⋙ GY' :=
  composeFunctorSquares (sheafHigherCoordinates.{a,m} f h n) (targetSectionsSquare.{max a m} f)

/-- The scalar-restricted side of the normalized site comparison of HA-H06. -/
def derivedAbutmentCoordinates (d : SiteTransportData.{max a m} f c c') (n : ℤ) :
    derivedTargetValue.{a,m} f n ⋙ LY ≅ d.site.functor ⋙
      (hypercohomology R' n ⋙ liftedRestriction.{max a m} f) :=
  d.restrictedCohomology f n

def sheafAbutmentCoordinates (d : SiteTransportData.{max a m} f c c') (n : ℕ) :
    sheafTargetValue.{a,m} f n ⋙ LY ≅ sheafInput.{a,m,u,v,r,s} (R := R) ⋙
      (sectionCohomology R' ⊤ n ⋙ liftedRestriction.{max a m} f) := by
  let I := LiftX ⋙ DerivedCategory.Plus.singleFunctor AX 0
  let H := hypercohomology R' (n : ℤ) ⋙ liftedRestriction.{max a m} f
  change I ⋙ (derivedTargetValue.{a,m} f (n : ℤ) ⋙ LY) ≅
    (sheafInput.{a,m,u,v,r,s} (R := R) ⋙ DerivedCategory.Plus.singleFunctor (Modules R') 0) ⋙ H
  exact isoWhiskerLeft I (derivedAbutmentCoordinates.{a,m} f d (n : ℤ)) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight (sheafStalkCoordinate.{a,m} f d) H

/-- The iterated side of the same normalized site comparison. -/
def iteratedAbutmentCoordinates (d : SiteTransportData.{max a m} f c c') (n : ℤ) :
    iteratedValue D GY n ⋙ LY ≅ d.site.functor ⋙ iteratedValue D' GY' n :=
  associator .. ≪≫ d.iterated.cohomology (D ⋙ GY) (D' ⋙ GY') JX LY n

variable (L : liftedLeray.{a,m} f) (d : SiteTransportData.{max a m} f c L.sections)
  (h : PageTransport.{a,m} f d)

def derivedSecondIso (p : ℕ) (q : ℤ) :
    derivedSequence.{a,m} f L d ⋙ pageEval 0 p ((p : ℤ) + q) ≅ derivedSecondValue.{a,m} f p q :=
  isoWhiskerRight (isoWhiskerLeft d.site.functor (L.derivedSecondIso p q)) B ≪≫
    lowerCoordinates.{a,m,u,v,r,s} (derivedPageCoordinates.{a,m} f h p q)

def sheafSecondIso (p q : ℕ) :
    sheafSequence.{a,m} f L ⋙ pageEval 0 p ((p : ℤ) + (q : ℤ)) ≅ sheafSecondValue.{a,m} f p q :=
  isoWhiskerRight (isoWhiskerLeft (sheafInput.{a,m,u,v,r,s} (R := R)) (L.sheafSecondIso p q)) B ≪≫
    lowerCoordinates.{a,m,u,v,r,s} (sheafPageCoordinates.{a,m} f h p q)

def derivedTargetIso (n : ℤ) :
    derivedSequence.{a,m} f L d ⋙ targetEval n ≅ derivedTargetValue.{a,m} f n :=
  isoWhiskerRight (isoWhiskerLeft d.site.functor (L.derivedTargetIso n)) B ≪≫
    lowerCoordinates.{a,m,u,v,r,s} (derivedAbutmentCoordinates.{a,m} f d n)

def sheafTargetIso (n : ℕ) :
    sheafSequence.{a,m} f L ⋙ targetEval (n : ℤ) ≅ sheafTargetValue.{a,m} f n :=
  isoWhiskerRight (isoWhiskerLeft (sheafInput.{a,m,u,v,r,s} (R := R)) (L.sheafTargetIso n)) B ≪≫
    lowerCoordinates.{a,m,u,v,r,s} (sheafAbutmentCoordinates.{a,m} f d n)

def derivedTargetViaComparison (n : ℤ) :
    derivedSequence.{a,m} f L d ⋙ targetEval n ≅ derivedTargetValue.{a,m} f n :=
  isoWhiskerRight (isoWhiskerLeft d.site.functor (L.package.iteratedIso n)) B ≪≫
    lowerCoordinates.{a,m,u,v,r,s} (iteratedAbutmentCoordinates.{a,m} f d n) ≪≫
    (c.cohomologyIso n).symm

def sequenceOnStalkIso :
    (LiftX ⋙ DerivedCategory.Plus.singleFunctor AX 0) ⋙ derivedSequence.{a,m} f L d ≅
      sheafSequence.{a,m} f L :=
  (associator _ _ _).symm ≪≫ isoWhiskerRight (sheafStalkCoordinate.{a,m} f d) _ ≪≫
    associator _ _ _

/-- The sequence on actual bounded-below complexes uses their termwise lift
and localization, with the induced maps on every page and filtration step. -/
abbrev originalComplexSequence :=
  originalComplexImage.{a,m,u,v,r,s} (R := R) ⋙ derivedSequence.{a,m} f L d

/-- Lifting the original degree-zero complex gives the stalk of the lifted
sheaf by the ordinary comparison for mapping single complexes. -/
def originalDegreeZeroIso :
    letI : HasZeroObject (SheafOfModules.{m} R) := hasZeroObject_of_hasTerminal_object
    degreeZeroComplex (SheafOfModules.{m} R) ⋙ originalComplexImage.{a,m,u,v,r,s} (R := R) ≅
      LiftX ⋙ DerivedCategory.Plus.singleFunctor AX 0 := by
  letI : HasZeroObject (SheafOfModules.{m} R) := hasZeroObject_of_hasTerminal_object
  apply ((FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight _).preimageIso
  change (CochainComplex.singleFunctor (SheafOfModules.{m} R) 0 ⋙
    (LiftX).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q ≅
      LiftX ⋙ DerivedCategory.singleFunctor AX 0
  exact isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex LiftX (.up ℤ) 0) _ ≪≫
    associator .. ≪≫ isoWhiskerLeft LiftX (DerivedCategory.singleFunctorIsoCompQ AX 0).symm

/-- The sheaf sequence is the specialization to the actual original
degree-zero complex. -/
def originalStalkSequenceIso :
    letI : HasZeroObject (SheafOfModules.{m} R) := hasZeroObject_of_hasTerminal_object
    degreeZeroComplex (SheafOfModules.{m} R) ⋙ originalComplexSequence.{a,m} f L d ≅
      sheafSequence.{a,m} f L := by
  letI : HasZeroObject (SheafOfModules.{m} R) := hasZeroObject_of_hasTerminal_object
  exact (associator _ _ _).symm ≪≫
    isoWhiskerRight (originalDegreeZeroIso.{a,m,u,v,r,s} (R := R)) _ ≪≫
    sequenceOnStalkIso.{a,m} f L d

open FiniteFiltrationConvergence in
/-- The canonical page-to-graded comparison on the lifted CE model. -/
def modelGradedIso (W : DerivedCategory.Plus (Modules S')) (k : ℕ) (p n : ℤ)
    (e : LimitIso (modelData GY' L.package.row W).filtration
      (modelData GY' L.package.row W).pages ((k : ℤ) + 2) p n) :
    (L.package.row.derived.obj W).page k p n ≅ cokernel ((L.package.row.derived.obj W).down p n) := by
  let i := modelIso GY' L.package.row W
  let g := cokernel.mapIso
    ((L.package.row.derived.obj W).down p n)
    ((diagram GY' (modelData GY' L.package.row W)).down p n)
    ((stepEval (p + 1) n).mapIso i) ((stepEval p n).mapIso i) (i.hom.down_comm p n).symm
  exact (pageEval k p n).mapIso i ≪≫ e.iso ≪≫ g.symm

open FiniteFiltrationConvergence in
/-- In each total degree the eventual comparison with the graded piece
carries the canonical quotient map of the lifted sequence. -/
def StableComparisons (W : DerivedCategory.Plus (Modules S')) : Prop :=
  ∀ n : ℤ, ∃ N : ℕ, ∀ (k : ℕ), N ≤ k → ∀ p : ℤ,
    ∃ e : LimitIso (modelData GY' L.package.row W).filtration
        (modelData GY' L.package.row W).pages ((k : ℤ) + 2) p n,
      let A := L.package.row.derived.obj W
      let i := modelGradedIso.{a,m} f L W k p n e
      let i' := changeGradedIso B A k p n i
      (changeCoefficientsObj B A).differential k p n = 0 ∧
        cokernel.π ((changeCoefficientsObj B A).down p n) ≫ i'.inv =
          (B).map (cokernel.π (A.down p n) ≫ i.inv)

/-- The two edges use the same target coordinates as the sequence. -/
def rowEdge (n : ℕ) : rowValue.{a,m} f n ⟶ sheafTargetValue.{a,m} f n :=
  (lowerCoordinates.{a,m,u,v,r,s} (rowCoordinates.{a,m} f h n)).inv ≫
    whiskerRight (whiskerLeft (sheafInput.{a,m,u,v,r,s} (R := R)) (L.rowEdge n)) B ≫
    (lowerCoordinates.{a,m,u,v,r,s} (sheafAbutmentCoordinates.{a,m} f d n)).hom

def columnEdge (n : ℕ) : sheafTargetValue.{a,m} f n ⟶ columnValue.{a,m} f n :=
  (lowerCoordinates.{a,m,u,v,r,s} (sheafAbutmentCoordinates.{a,m} f d n)).inv ≫
    whiskerRight (whiskerLeft (sheafInput.{a,m,u,v,r,s} (R := R)) (L.columnEdge n)) B ≫
    (lowerCoordinates.{a,m,u,v,r,s} (columnCoordinates.{a,m} f h n)).hom

def rowPageIso (n : ℕ) :
    sheafSequence.{a,m} f L ⋙ pageEval 0 (n : ℤ) (n : ℤ) ≅ rowValue.{a,m} f n :=
  isoWhiskerRight (isoWhiskerLeft (sheafInput.{a,m,u,v,r,s} (R := R)) (L.edges.rowPage n)) B ≪≫
    lowerCoordinates.{a,m,u,v,r,s} (rowCoordinates.{a,m} f h n)

def columnPageIso (n : ℕ) :
    sheafSequence.{a,m} f L ⋙ pageEval 0 0 (n : ℤ) ≅ columnValue.{a,m} f n :=
  isoWhiskerRight (isoWhiskerLeft (sheafInput.{a,m,u,v,r,s} (R := R)) (L.edges.columnPage n)) B ≪≫
    lowerCoordinates.{a,m,u,v,r,s} (columnCoordinates.{a,m} f h n)

/-- The filtration on the stated original-ring abutment. Its presentation by
the transported diagram carries the associated graded cokernels. -/
def filtration (K : DerivedCategory.Plus AX) (p n : ℤ) :
    Subobject ((derivedTargetValue.{a,m} f n).obj K) :=
  imageSubobject (((derivedSequence.{a,m} f L d).obj K).inclusion p n ≫
    (derivedTargetIso.{a,m} f L d n).hom.app K)

/-- The coordinates, convergence and both degenerations on the original data. -/
structure LerayComparison : Prop where
  cohomology_commutes : d.CohomologyCoherence f
  derived_target : ∀ n, derivedTargetIso.{a,m} f L d n =
    derivedTargetViaComparison.{a,m} f L d n
  sheaf_target : ∀ (M : SheafOfModules.{m} R) (n : ℕ),
    ((sequenceOnStalkIso.{a,m} f L d).hom.app M).target (n : ℤ) ≫
      (sheafTargetIso.{a,m} f L d n).hom.app M =
    (derivedTargetIso.{a,m} f L d n).hom.app
      ((DerivedCategory.Plus.singleFunctor AX 0).obj ((LiftX).obj M))
  sheaf_second : ∀ (M : SheafOfModules.{m} R) (p q : ℕ),
    ((sequenceOnStalkIso.{a,m} f L d).hom.app M).page 0 (p : ℤ) ((p : ℤ) + (q : ℤ)) ≫
      (sheafSecondIso.{a,m} f L d h p q).hom.app M =
    (derivedSecondIso.{a,m} f L d h p (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor AX 0).obj ((LiftX).obj M))
  finite_derived : ∀ (K : DerivedCategory.Plus AX), FilteredAbutment ((derivedSequence.{a,m} f L d).obj K)
  finite_sheaf : ∀ (M : SheafOfModules.{m} R), FilteredAbutment ((sheafSequence.{a,m} f L).obj M)
  stable_derived : ∀ (K : DerivedCategory.Plus AX),
    StableComparisons.{a,m} f L ((D').rightDerivedFunctorPlus.obj
      (d.site.functor.obj K))
  stable_sheaf : ∀ (M : SheafOfModules.{m} R),
    StableComparisons.{a,m} f L ((D').rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Modules R') 0).obj
        ((sheafInput.{a,m,u,v,r,s} (R := R)).obj M)))
  original_lower_bound : ∀ (K : CochainComplex.Plus (SheafOfModules.{m} R)) (b : ℤ),
    K.obj.IsStrictlyGE b → ((originalComplexImage.{a,m,u,v,r,s} (R := R)).obj K).IsGE b
  derived_support : ∀ (K : DerivedCategory.Plus AX) (b : ℤ), K.IsGE b →
    ∀ (r : ℕ) (p n : ℤ), p < 0 ∨ n - p < b →
      IsZero (((derivedSequence.{a,m} f L d).obj K).page r p n)
  derived_bounds : ∀ (K : DerivedCategory.Plus AX) (b : ℤ), K.IsGE b →
    ∀ p n : ℤ, (p ≤ 0 → IsIso (((derivedSequence.{a,m} f L d).obj K).inclusion p n)) ∧
      (n - b < p → IsZero (((derivedSequence.{a,m} f L d).obj K).step p n))
  sheaf_support : ∀ (M : SheafOfModules.{m} R) (r : ℕ) (p n : ℤ), p < 0 ∨ n < p →
    IsZero (((sheafSequence.{a,m} f L).obj M).page r p n)
  sheaf_bounds : ∀ (M : SheafOfModules.{m} R) (p n : ℤ),
    (p ≤ 0 → IsIso (((sheafSequence.{a,m} f L).obj M).inclusion p n)) ∧
      (n < p → IsZero (((sheafSequence.{a,m} f L).obj M).step p n))
  row_square : ∀ (M : SheafOfModules.{m} R) (n : ℕ),
    (rowPageIso.{a,m} f L d h n).hom.app M ≫ (rowEdge.{a,m} f L d h n).app M =
      (B).map ((L.edges.filtered ((sheafInput.{a,m,u,v,r,s} (R := R)).obj M)).row n) ≫
        (sheafTargetIso.{a,m} f L d n).hom.app M
  column_square : ∀ (M : SheafOfModules.{m} R) (n : ℕ),
    (sheafTargetIso.{a,m} f L d n).hom.app M ≫ (columnEdge.{a,m} f L d h n).app M =
      (B).map ((L.edges.filtered ((sheafInput.{a,m,u,v,r,s} (R := R)).obj M)).column n) ≫
        (columnPageIso.{a,m} f L d h n).hom.app M
  row_isIso : ∀ (M : SheafOfModules.{m} R),
    (∀ q : ℕ, 0 < q → IsZero ((originalHigherValue.{a,m} f q).obj M)) →
    ∀ n : ℕ, IsIso ((rowEdge.{a,m} f L d h n).app M)
  column_isIso : ∀ (M : SheafOfModules.{m} R),
    (∀ p q : ℕ, 0 < p → IsZero ((sheafSecondValue.{a,m} f p q).obj M)) →
    ∀ n : ℕ, IsIso ((columnEdge.{a,m} f L d h n).app M)

end AdvancedHomologicalAlgebra.LerayIndependentCoefficients

namespace Specs.AdvancedHomologicalAlgebra.LerayIndependentCoefficients

open _root_.AdvancedHomologicalAlgebra.LerayIndependentCoefficients
open _root_.AdvancedHomologicalAlgebra.OriginalDerivedSectionsTheory
open _root_.AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory
open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

universe a m u v r s

attribute [local instance] HasDerivedCategory.standard

/-- Global Leray for the actual original ringed map, with the two edge
isomorphisms under their separate vanishing hypotheses. -/
def globalLerayType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S),
    letI := sectionHasSheafify.{max a m v r s,u} X
    letI := sectionWEqualsLocallyBijective.{max a m v r s,u} X
    letI := sectionHasSheafify.{max a m u r s,v} Y
    letI := sectionWEqualsLocallyBijective.{max a m u r s,v} Y
    ∃ (hX : EnoughInjectives (AmbientSheaves.{max a m v s} R))
      (hY : EnoughInjectives (AmbientSheaves.{max a m u r} S))
      (eX : (transport.{max a m v s} R).IsEquivalence)
      (eY : (transport.{max a m u r} S).IsEquivalence),
      letI := hX
      letI := hY
      letI := eX
      letI := eY
      ∃ (L : liftedLeray.{a,m} f) (c : SectionsData.{max a m} f)
        (d : SiteTransportData.{max a m} f c L.sections) (h : PageTransport.{a,m} f d),
        c.IsModelComparison f ∧ LerayComparison.{a,m} f L d h

end Specs.AdvancedHomologicalAlgebra.LerayIndependentCoefficients
