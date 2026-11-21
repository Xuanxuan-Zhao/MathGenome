import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedSectionsComposition
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients

/-! HA-H06 on the original sites and rings, after enlarging the coefficient
universe. Functor composition is written in diagrammatic order. -/
noncomputable section
set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
universe a b m u v r s

namespace AdvancedHomologicalAlgebra.OriginalDerivedSectionsTheory

abbrev globalSections {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) :=
  sectionsValue.{a} R (⊤ : Opens X)

section
variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)

abbrev scalarRestriction :=
  sectionScalars.{max a u v r s} f (⊤ : Opens Y)

set_option hygiene false in
local notation "D" => ambientDirectImage.{a} f
set_option hygiene false in
local notation "ΓX" => globalSections.{max a v s} R
set_option hygiene false in
local notation "ΓY" => globalSections.{max a u r} S
set_option hygiene false in
local notation "Res" => scalarRestriction.{a} f

/-- The identity on sections over the whole space, with its original scalar
action restricted by the given map of ringed spaces. -/
def sectionsIdentity : D ⋙ ΓY ≅ ΓX ⋙ Res :=
  Iso.refl _

/-- This follows the actual section-ring isomorphism at the whole space. -/
abbrev sourceScalars (_ : RingedMap R S) := liftedScalars.{max a v s} R (⊤ : Opens (liftedSpace.{max a u v r s} X))

abbrev targetScalars (_ : RingedMap R S) := liftedScalars.{max a u r} S (⊤ : Opens (liftedSpace.{max a u v r s} Y))

abbrev liftedRestriction :=
  AdvancedHomologicalAlgebra.DerivedSectionsTheory.scalarRestriction
    (liftedRing.{max a v s} R) (liftedRing.{max a u r} S)
    (transportedMap.{a} f) (transportedScalars.{a} f)

/-- The scalar square is the identity on the underlying section groups. -/
def scalarSquare : Res ⋙ targetScalars.{a} f ≅
    sourceScalars.{a} f ⋙ liftedRestriction.{a} f :=
  NatIso.ofComponents (fun M ↦
    let P := (Res ⋙ targetScalars.{a} f).obj M
    let Q := (sourceScalars.{a} f ⋙ liftedRestriction.{a} f).obj M
    let e : (P : Type (max a u v r s)) ≃ₗ[(liftedRing.{max a u r} S).obj.obj (op ⊤)]
        (Q : Type (max a u v r s)) :=
      { toAddEquiv := AddEquiv.refl _, map_smul' := fun _ _ ↦ rfl }
    e.toModuleIso)
    (by intros; ext x; rfl)

abbrev sourceSectionsSquare (_ : RingedMap R S) :=
  siteSectionsIso.{max a v s} R (⊤ : Opens (liftedSpace.{max a u v r s} X))

abbrev targetSectionsSquare (_ : RingedMap R S) :=
  siteSectionsIso.{max a u r} S (⊤ : Opens (liftedSpace.{max a u v r s} Y))

set_option hygiene false in
local notation "JX" => transport.{max a v s} R
set_option hygiene false in
local notation "JY" => transport.{max a u r} S
set_option hygiene false in
local notation "DX" => transportedDirectImage.{a} f
set_option hygiene false in
local notation "LX" => AdvancedHomologicalAlgebra.DerivedSectionsTheory.globalSections (liftedRing.{max a v s} R)
set_option hygiene false in
local notation "LY" => AdvancedHomologicalAlgebra.DerivedSectionsTheory.globalSections (liftedRing.{max a u r} S)
set_option hygiene false in
local notation "HX" => sourceScalars.{a} f
set_option hygiene false in
local notation "HY" => targetScalars.{a} f

abbrev liftedSectionsIdentity :=
  AdvancedHomologicalAlgebra.DerivedSectionsTheory.sectionsIdentity
    (liftedRing.{max a v s} R) (liftedRing.{max a u r} S)
    (transportedMap.{a} f) (transportedScalars.{a} f)

/-- The square obtained by changing sites in the pushforward and evaluating
at the terminal open of the target. -/
def compositeSquare : (D ⋙ ΓY) ⋙ HY ≅ JX ⋙ (DX ⋙ LY) :=
  associator .. ≪≫ isoWhiskerLeft D (targetSectionsSquare.{a} f) ≪≫
    (associator ..).symm ≪≫
    isoWhiskerRight (Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients.pushforwardTransportExpected.{a,u,v,r,s} f) LY ≪≫
    associator ..

/-- The same square along sections on the source and scalar restriction. -/
def restrictedSquare : (ΓX ⋙ Res) ⋙ HY ≅ JX ⋙ (LX ⋙ liftedRestriction.{a} f) :=
  associator .. ≪≫ isoWhiskerLeft ΓX (scalarSquare.{a} f) ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight (sourceSectionsSquare.{a} f) _ ≪≫
    associator ..

end

section Models
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- Inclusion of the exact descent on bounded-below categories and the actual
factorization of localization on complexes. -/
structure ExactDescent (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
    [PreservesFiniteColimits T] where
  functor : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B
  termwise : functor ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ T.mapDerivedCategory
  factors : DerivedCategory.Plus.Q ⋙ functor ≅ T.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q
  factors_on_complex : ∀ K : CochainComplex.Plus A,
    (DerivedCategory.Plus.ι).map (factors.inv.app K) ≫ termwise.hom.app (DerivedCategory.Plus.Q.obj K) =
      T.mapDerivedCategoryFactors.inv.app K.obj
  cohomology (n : ℤ) : functor ⋙ DerivedCategory.Plus.homologyFunctor B n ≅
    DerivedCategory.Plus.homologyFunctor A n ⋙ T
  cohomology_on_complex : ∀ (n : ℤ) (K : CochainComplex.Plus A),
    (cohomology n).hom.app (DerivedCategory.Plus.Q.obj K) =
      (DerivedCategory.Plus.homologyFunctor B n).map (factors.hom.app K) ≫
      (DerivedCategory.homologyFunctorFactors B n).hom.app
        ((T.mapHomologicalComplex (.up ℤ)).obj K.obj) ≫
      ((K.obj.sc n).mapHomologyIso T).hom ≫
      T.map ((DerivedCategory.homologyFunctorFactors A n).inv.app K.obj)

/-- The exact descent also realizes the actual right-derived unit. -/
def ExactDescent.UnitCompatibility (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
    [PreservesFiniteColimits T] [EnoughInjectives A] (d : ExactDescent T) : Prop :=
  ∃ e : T.rightDerivedFunctorPlus ≅ d.functor,
    ∀ K : CochainComplex.Plus A,
      T.rightDerivedFunctorPlusUnit.app K ≫ e.hom.app (DerivedCategory.Plus.Q.obj K) =
        d.factors.inv.app K


end Models

section FunctorSquares

variable {A A' B B' C C' : Type*}
  [Category* A] [Category* A'] [Category* B] [Category* B'] [Category* C] [Category* C']
  {F : A ⥤ B} {F' : A' ⥤ B'} {G : B ⥤ C} {G' : B' ⥤ C'}
  {J : A ⥤ A'} {H : B ⥤ B'} {T : C ⥤ C'}

/-- Compose comparison squares along the common intermediate functor. -/
def composeFunctorSquares (e : F ⋙ H ≅ J ⋙ F') (d : G ⋙ T ≅ H ⋙ G') :
    (F ⋙ G) ⋙ T ≅ J ⋙ (F' ⋙ G') :=
  associator .. ≪≫ isoWhiskerLeft F d ≪≫ (associator ..).symm ≪≫
    isoWhiskerRight e G' ≪≫ associator ..

end FunctorSquares

section Composition

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- Before localization the two ways of applying a composite on complexes
have the same terms and differentials. -/
def complexComposition :
    (F ⋙ G).mapCochainComplexPlus ≅ F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _))
    (by intros; apply (CochainComplex.Plus.ι C).map_injective
        ext n; simp)

/-- Apply the model comparisons for both functors of a composite. -/
def compositeUnit {L : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {M : DerivedCategory.Plus B ⥤ DerivedCategory.Plus C}
    (η : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L)
    (θ : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ M) :
    (F ⋙ G).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ (L ⋙ M) :=
  whiskerRight (complexComposition F G).hom _ ≫
    (associator ..).hom ≫ whiskerLeft F.mapCochainComplexPlus θ ≫
    (associator ..).inv ≫ whiskerRight η _ ≫ (associator ..).hom

variable [EnoughInjectives A]

/-- Apply the actual two right-derived units to the ordinary composite. -/
def iteratedUnit [EnoughInjectives B] :
    (F ⋙ G).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) :=
  whiskerRight (complexComposition F G).hom _ ≫
    (associator ..).hom ≫ whiskerLeft F.mapCochainComplexPlus G.rightDerivedFunctorPlusUnit ≫
    (associator ..).inv ≫ whiskerRight F.rightDerivedFunctorPlusUnit _ ≫ (associator ..).hom

/-- The unit for the exact postcomposition, before localization. -/
def termwiseUnit [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : ExactDescent G) :
    (F ⋙ G).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ (F.rightDerivedFunctorPlus ⋙ e.functor) :=
  whiskerRight (complexComposition F G).hom _ ≫
    (associator ..).hom ≫ whiskerLeft F.mapCochainComplexPlus e.factors.inv ≫
    (associator ..).inv ≫ whiskerRight F.rightDerivedFunctorPlusUnit _ ≫ (associator ..).hom


end Composition

section Transport

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  (F : A ⥤ B) (G : A' ⥤ B') (J : A ⥤ A') (H : B ⥤ B')
  [F.Additive] [G.Additive] [J.Additive] [H.Additive]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The ordinary square on the terms and differentials of a complex. -/
def complexSquare (c : F ⋙ H ≅ J ⋙ G) :
    F.mapCochainComplexPlus ⋙ H.mapCochainComplexPlus ≅
      J.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus :=
  NatIso.ofComponents (fun I ↦ ObjectProperty.isoMk _
    ((NatIso.mapHomologicalComplex c (.up ℤ)).app I.obj))
    (fun g ↦ (CochainComplex.Plus.ι B').map_injective
      ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.naturality g.hom))

/-- The localized square extends the ordinary square with the indicated units. -/
def RespectsModelUnits (c : F ⋙ H ≅ J ⋙ G) (j : ExactDescent J) (h : ExactDescent H)
    {L : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {L' : DerivedCategory.Plus A' ⥤ DerivedCategory.Plus B'}
    (η : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L)
    (η' : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L')
    (e : L ⋙ h.functor ≅ j.functor ⋙ L') (I : CochainComplex.Plus A) : Prop :=
  h.functor.map (η.app I) ≫ e.hom.app (DerivedCategory.Plus.Q.obj I) =
    h.factors.hom.app (F.mapCochainComplexPlus.obj I) ≫
    DerivedCategory.Plus.Q.map ((complexSquare F G J H c).hom.app I) ≫
    η'.app (J.mapCochainComplexPlus.obj I) ≫ L'.map (j.factors.inv.app I)

/-- A comparison of derived functors fixed by the actual model maps on complexes. -/
structure UnitTransport (c : F ⋙ H ≅ J ⋙ G) (j : ExactDescent J) (h : ExactDescent H)
    {L : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {L' : DerivedCategory.Plus A' ⥤ DerivedCategory.Plus B'}
    (η : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L)
    (η' : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L') where
  iso : L ⋙ h.functor ≅ j.functor ⋙ L'
  on_complex : ∀ I, RespectsModelUnits F G J H c j h η η' iso I

/-- A derived transport whose components are fixed by the ordinary square
and the two specified model maps. -/
structure ModelTransport (c : F ⋙ H ≅ J ⋙ G)
    (j : ExactDescent J) (h : ExactDescent H)
    {L : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {L' : DerivedCategory.Plus A' ⥤ DerivedCategory.Plus B'}
    (η : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L)
    (η' : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L') where
  iso : L ⋙ h.functor ≅ j.functor ⋙ L'
  on_injective : ∀ I : CochainComplex.Plus A, (∀ n : ℤ, Injective (I.obj.X n)) →
    h.functor.map (η.app I) ≫ iso.hom.app (DerivedCategory.Plus.Q.obj I) =
      h.factors.hom.app (F.mapCochainComplexPlus.obj I) ≫
      DerivedCategory.Plus.Q.map ((complexSquare F G J H c).hom.app I) ≫
      η'.app (J.mapCochainComplexPlus.obj I) ≫ L'.map (j.factors.inv.app I)

/-- Apply cohomology to the same derived transport, using the exact scalar
comparison of the coefficients. -/
def ModelTransport.cohomology {c : F ⋙ H ≅ J ⋙ G}
    {j : ExactDescent J} {h : ExactDescent H}
    {L : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {L' : DerivedCategory.Plus A' ⥤ DerivedCategory.Plus B'}
    {η : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L}
    {η' : G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ L'}
    (e : ModelTransport F G J H c j h η η') (n : ℤ) :
    L ⋙ (DerivedCategory.Plus.homologyFunctor B n ⋙ H) ≅
      j.functor ⋙ (L' ⋙ DerivedCategory.Plus.homologyFunctor B' n) :=
  isoWhiskerLeft L (h.cohomology n).symm ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight e.iso _ ≪≫ associator ..

end Transport


section

variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)

variable [HasSheafify (Opens.grothendieckTopology X)
    AddCommGrpCat.{max a u v r s}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{max a u v r s}]
variable [HasSheafify (Opens.grothendieckTopology Y)
    AddCommGrpCat.{max a u v r s}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max a u v r s}]
attribute [local instance] HasDerivedCategory.standard

set_option hygiene false in
local notation "A" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "B" => AmbientSheaves.{max a u r} S
set_option hygiene false in
local notation "D" => ambientDirectImage.{a} f
set_option hygiene false in
local notation "ΓX" => globalSections.{max a v s} R
set_option hygiene false in
local notation "ΓY" => globalSections.{max a u r} S
set_option hygiene false in
local notation "Res" => scalarRestriction.{a} f
set_option hygiene false in
local notation "SY" => SectionModules.{max a u r} S (⊤ : Opens Y)

variable [EnoughInjectives A] [EnoughInjectives B]

/-- The comparison with exact scalar restriction, with both units evaluated
on the same ambient injective complex. The other leg is the actual
composition transformation of HA-R12. -/
structure SectionsData where
  restriction : ExactDescent Res
  restriction_unit : ExactDescent.UnitCompatibility Res restriction
  comparison : (D ⋙ ΓY).rightDerivedFunctorPlus ≅ (ΓX).rightDerivedFunctorPlus ⋙ restriction.functor
  on_injective : ∀ (I : CochainComplex.Plus A), (∀ j : ℤ, Injective (I.obj.X j)) →
    (D ⋙ ΓY).rightDerivedFunctorPlusUnit.app I ≫ comparison.hom.app (DerivedCategory.Plus.Q.obj I) =
      DerivedCategory.Plus.Q.map
        (((sectionsIdentity.{a} f).hom.mapCochainComplexPlus).app I) ≫
      (termwiseUnit ΓX Res restriction).app I
  composition_isIso : IsIso
    (Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue D ΓY)

abbrev liftedSectionsData :=
  AdvancedHomologicalAlgebra.DerivedSectionsTheory.SectionsDerivedData
    (liftedRing.{max a v s} R) (liftedRing.{max a u r} S)
    (transportedMap.{a} f) (transportedScalars.{a} f)


variable {f}

/-- The normalized comparison on the whole derived category. -/
def SectionsData.iteratedIso (c : SectionsData.{a} f) :
    (ΓX).rightDerivedFunctorPlus ⋙ c.restriction.functor ≅
      (D).rightDerivedFunctorPlus ⋙ (ΓY).rightDerivedFunctorPlus := by
  letI := c.composition_isIso
  exact c.comparison.symm ≪≫
    asIso (Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue D ΓY)

/-- Its cohomology, in the original target section-ring coordinates. -/
def SectionsData.cohomologyIso (c : SectionsData.{a} f) (n : ℤ) :
    (ΓX).rightDerivedFunctorPlus ⋙ (DerivedCategory.Plus.homologyFunctor _ n ⋙ Res) ≅
      ((D).rightDerivedFunctorPlus ⋙ (ΓY).rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor SY n :=
  isoWhiskerLeft (ΓX).rightDerivedFunctorPlus (c.restriction.cohomology n).symm ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight c.iteratedIso _

/-- The exact coefficient lift is used on the complex before any right
derived functor is evaluated. -/
abbrev coefficientLift (_ : RingedMap R S) :=
  liftSheafCoefficients.{max a u v r s,u,r,m} R

variable [HasSheafify (Opens.grothendieckTopology X)
    AddCommGrpCat.{max a m u v r s}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{max a m u v r s}]
variable [HasSheafify (Opens.grothendieckTopology Y)
    AddCommGrpCat.{max a m u v r s}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max a m u v r s}]
variable [EnoughInjectives (AmbientSheaves.{max a m v s} R)]
  [EnoughInjectives (AmbientSheaves.{max a m u r} S)]

/-- Evaluation of the comparison after the coefficient lift and localization,
natural in maps of the original bounded-below complexes. -/
def SectionsData.onOriginalComplexes (c : SectionsData.{max a m} f) :=
  isoWhiskerLeft ((coefficientLift.{a,m,u,v,r,s} f).mapCochainComplexPlus ⋙
    DerivedCategory.Plus.Q) c.iteratedIso

def SectionsData.onOriginalCohomology (c : SectionsData.{max a m} f) (n : ℤ) :=
  isoWhiskerLeft ((coefficientLift.{a,m,u,v,r,s} f).mapCochainComplexPlus ⋙
    DerivedCategory.Plus.Q) (c.cohomologyIso n)

/-- The same cohomology comparison on sheaves, naturally in the original
coefficient, by placing its ambient lift in degree zero. -/
def SectionsData.onOriginalSheaves (c : SectionsData.{max a m} f) (n : ℕ) :
    coefficientLift.{a,m,u,v,r,s} f ⋙
      (cohomologyValue.{max a m v s} R (⊤ : Opens X) n ⋙ scalarRestriction.{max a m} f) ≅
    coefficientLift.{a,m,u,v,r,s} f ⋙
      (DerivedCategory.Plus.singleFunctor (AmbientSheaves.{max a m v s} R) 0 ⋙
        (((ambientDirectImage.{max a m} f).rightDerivedFunctorPlus ⋙
          (globalSections.{max a m u r} S).rightDerivedFunctorPlus) ⋙
          DerivedCategory.Plus.homologyFunctor _ (n : ℤ))) :=
  isoWhiskerLeft
    (coefficientLift.{a,m,u,v,r,s} f ⋙
      DerivedCategory.Plus.singleFunctor (AmbientSheaves.{max a m v s} R) 0)
    (c.cohomologyIso (n : ℤ))

end

section SiteTransport

variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a u v r s}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a u v r s}]
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a u v r s}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a u v r s}]
attribute [local instance] HasDerivedCategory.standard

set_option hygiene false in
local notation "A" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "B" => AmbientSheaves.{max a u r} S
set_option hygiene false in
local notation "D" => ambientDirectImage.{a} f
set_option hygiene false in
local notation "ΓX" => globalSections.{max a v s} R
set_option hygiene false in
local notation "ΓY" => globalSections.{max a u r} S
set_option hygiene false in
local notation "Res" => scalarRestriction.{a} f
set_option hygiene false in
local notation "J" => transport.{max a v s} R
set_option hygiene false in
local notation "H" => targetScalars.{a} f
set_option hygiene false in
local notation "DX" => transportedDirectImage.{a} f
set_option hygiene false in
local notation "LX" => AdvancedHomologicalAlgebra.DerivedSectionsTheory.globalSections (liftedRing.{max a v s} R)
set_option hygiene false in
local notation "LY" => AdvancedHomologicalAlgebra.DerivedSectionsTheory.globalSections (liftedRing.{max a u r} S)
set_option hygiene false in
local notation "LT" => liftedRestriction.{a} f

variable [EnoughInjectives A] [EnoughInjectives B]
variable [(J).IsEquivalence]

/-- The exact termwise coordinates of the accepted comparison. -/
structure LiftedRestrictionCoordinates (c : liftedSectionsData.{a} f) where
  descent : ExactDescent LT
  identify : (LT).rightDerivedFunctorPlus ≅ descent.functor
  termwise : isoWhiskerRight identify DerivedCategory.Plus.ι ≪≫ descent.termwise =
    c.restriction.termwise
  homology : ∀ n : ℤ, descent.cohomology n =
    isoWhiskerRight descent.termwise (DerivedCategory.homologyFunctor _ n) ≪≫
      associator .. ≪≫ isoWhiskerLeft DerivedCategory.Plus.ι (c.restriction.homology n) ≪≫
      (associator ..).symm

def LiftedRestrictionCoordinates.comparison {c : liftedSectionsData.{a} f}
    (e : LiftedRestrictionCoordinates.{a} f c) :
    (DX ⋙ LY).rightDerivedFunctorPlus ≅ (LX).rightDerivedFunctorPlus ⋙ e.descent.functor :=
  c.comparison ≪≫ isoWhiskerLeft _ e.identify

def LiftedRestrictionCoordinates.iterated {c : liftedSectionsData.{a} f}
    (e : LiftedRestrictionCoordinates.{a} f c) :
    (LX).rightDerivedFunctorPlus ⋙ e.descent.functor ≅
      (DX).rightDerivedFunctorPlus ⋙ (LY).rightDerivedFunctorPlus :=
  (isoWhiskerLeft _ e.identify).symm ≪≫ c.iteratedIso

/-- Insert the ordinary sections identity before applying the exact
postcomposition unit. -/
def sectionsTermwiseUnit (t : ExactDescent Res) :
    (D ⋙ ΓY).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ ((ΓX).rightDerivedFunctorPlus ⋙ t.functor) :=
  whiskerRight (sectionsIdentity.{a} f).hom.mapCochainComplexPlus _ ≫ termwiseUnit ΓX Res t

def liftedTermwiseUnit (t : ExactDescent LT) :
    (DX ⋙ LY).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ ((LX).rightDerivedFunctorPlus ⋙ t.functor) :=
  whiskerRight (liftedSectionsIdentity.{a} f).hom.mapCochainComplexPlus _ ≫
    termwiseUnit LX LT t

/-- The comparison sends the restricted section complex of an injective
model to the iterated value via the units of pushforward and sections.
Taking cohomology of this equation uses the exact scalar comparison. -/
def SectionsData.ModelEquation (c : SectionsData.{a} f) (I : CochainComplex.Plus A) : Prop :=
  let K := DerivedCategory.Plus.Q.obj I
  let h := sectionsTermwiseUnit.{a} f c.restriction
  let Hn (n : ℤ) := DerivedCategory.Plus.homologyFunctor _ n
  (h.app I ≫ c.iteratedIso.hom.app K = (iteratedUnit D ΓY).app I) ∧
    ∀ n : ℤ,
      (Hn n).map (h.app I) ≫
        (c.restriction.cohomology n).hom.app ((ΓX).rightDerivedFunctorPlus.obj K) ≫
        (c.cohomologyIso n).hom.app K =
      (Hn n).map ((iteratedUnit D ΓY).app I)

def SectionsData.IsModelComparison (c : SectionsData.{a} f) : Prop :=
  ∀ (I : CochainComplex.Plus A), (∀ k : ℤ, Injective (I.obj.X k)) → c.ModelEquation f I

/-- The vertical maps are required to match the original termwise maps.
The horizontal maps are the original comparison and the accepted
same-universe comparison, viewed in their exact scalar coordinates. -/
structure SiteTransportData (c : SectionsData.{a} f) (c' : liftedSectionsData.{a} f) where
  coordinates : LiftedRestrictionCoordinates.{a} f c'
  site : ExactDescent J
  scalars : ExactDescent H
  restricted :
    ModelTransport _ _ J H (compositeSquare.{a} f) site scalars
      (sectionsTermwiseUnit.{a} f c.restriction)
      (liftedTermwiseUnit.{a} f coordinates.descent)
  iterated :
    ModelTransport _ _ J H (compositeSquare.{a} f) site scalars
      (iteratedUnit D ΓY) (iteratedUnit DX LY)
  commutes : ∀ K : DerivedCategory.Plus A,
    scalars.functor.map (c.iteratedIso.hom.app K) ≫ iterated.iso.hom.app K =
      restricted.iso.hom.app K ≫ (coordinates.iterated f).hom.app (site.functor.obj K)

/-- Apply cohomology to the same accepted comparison after putting exact
restriction in its termwise coordinates. -/
def LiftedRestrictionCoordinates.cohomologyIso {c' : liftedSectionsData.{a} f}
    (e : LiftedRestrictionCoordinates.{a} f c') (n : ℤ) :
    (LX).rightDerivedFunctorPlus ⋙ (DerivedCategory.Plus.homologyFunctor _ n ⋙ LT) ≅
      ((DX).rightDerivedFunctorPlus ⋙ (LY).rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor _ n :=
  isoWhiskerLeft (LX).rightDerivedFunctorPlus (e.descent.cohomology n).symm ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight (e.iterated f) _

variable {c : SectionsData.{a} f} {c' : liftedSectionsData.{a} f}

/-- The transport on the restricted cohomology has the original scalar
restriction as its source and the lifted scalar restriction as its target. -/
def SiteTransportData.restrictedCohomology (d : SiteTransportData.{a} f c c') (n : ℤ) :
    (((ΓX).rightDerivedFunctorPlus ⋙ (DerivedCategory.Plus.homologyFunctor _ n ⋙ Res)) ⋙ H) ≅
      d.site.functor ⋙ ((LX).rightDerivedFunctorPlus ⋙ (DerivedCategory.Plus.homologyFunctor _ n ⋙ LT)) :=
  isoWhiskerRight (isoWhiskerLeft (ΓX).rightDerivedFunctorPlus
    (c.restriction.cohomology n).symm ≪≫ (associator ..).symm) H ≪≫
    associator .. ≪≫ d.restricted.cohomology _ _ J H n ≪≫
    isoWhiskerLeft d.site.functor
      (associator .. ≪≫ isoWhiskerLeft (LX).rightDerivedFunctorPlus (d.coordinates.descent.cohomology n))

/-- Cohomology commutes with transport for the very same derived comparison. -/
def SiteTransportData.CohomologyCoherence (d : SiteTransportData.{a} f c c') : Prop :=
  ∀ (K : DerivedCategory.Plus A) (n : ℤ),
    (H).map ((c.cohomologyIso n).hom.app K) ≫
      (d.iterated.cohomology _ _ J H n).hom.app K =
    (d.restrictedCohomology f n).hom.app K ≫
      (d.coordinates.cohomologyIso f n).hom.app (d.site.functor.obj K)

/-- Compare this normalized sections isomorphism with the same-universe
comparison in the site and ring coordinates. -/
def SectionsData.SiteCoherence (c : SectionsData.{a} f) : Prop :=
  ∃ (_ : (J).IsEquivalence), ∀ c' : liftedSectionsData.{a} f,
    ∃ d : SiteTransportData.{a} f c c', d.CohomologyCoherence f

end SiteTransport


section OriginalCoefficients

variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)

set_option hygiene false in
local notation "D₀" => directImageValue.{m} f
set_option hygiene false in
local notation "ΓX₀" => SheafOfModules.evaluation.{m} R (op (⊤ : Opens X))
set_option hygiene false in
local notation "ΓY₀" => SheafOfModules.evaluation.{m} S (op (⊤ : Opens Y))
set_option hygiene false in
local notation "Res₀" => sectionScalars.{m} f (⊤ : Opens Y)
set_option hygiene false in
local notation "D₁" => ambientDirectImage.{max a m} f
set_option hygiene false in
local notation "ΓX₁" => globalSections.{max a m v s} R
set_option hygiene false in
local notation "ΓY₁" => globalSections.{max a m u r} S
set_option hygiene false in
local notation "Res₁" => scalarRestriction.{max a m} f
set_option hygiene false in
local notation "LX₀" => coefficientLift.{a,m,u,v,r,s} f
set_option hygiene false in
local notation "HX₀" => ModuleCat.uliftFunctor.{max a u v r s,m} (R.obj.obj (op ⊤))
set_option hygiene false in
local notation "HY₀" => ModuleCat.uliftFunctor.{max a u v r s,m} (S.obj.obj (op ⊤))

/-- The original section identity already holds before enlarging coefficients. -/
def smallSectionsIdentity : D₀ ⋙ ΓY₀ ≅ ΓX₀ ⋙ Res₀ :=
  Iso.refl _

/-- Lifting section carriers commutes with restriction along the original
ring map, via the identity on the lifted sections. -/
def coefficientScalarSquare : Res₀ ⋙ HY₀ ≅ HX₀ ⋙ Res₁ :=
  NatIso.ofComponents (fun M ↦
    let P := (Res₀ ⋙ HY₀).obj M
    let Q := (HX₀ ⋙ Res₁).obj M
    let e : (P : Type (max a m u v r s)) ≃ₗ[S.obj.obj (op ⊤)] (Q : Type (max a m u v r s)) :=
      { toAddEquiv := AddEquiv.refl _, map_smul' := fun _ _ ↦ rfl }
    e.toModuleIso) (by intros; ext x; rfl)

/-- Change the coefficient size in pushforward and in global evaluation. -/
def coefficientCompositeSquare : (D₀ ⋙ ΓY₀) ⋙ HY₀ ≅ LX₀ ⋙ (D₁ ⋙ ΓY₁) :=
  associator .. ≪≫ isoWhiskerLeft D₀
    (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{max a u v r s,v,s,m} Y S ⊤).symm ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight
      (Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients.coefficientLiftComparisonValue.{max a u v r s,m,u,v,r,s} f) ΓY₁ ≪≫
    associator ..

/-- Change the coefficient size in global sections on the source and then
restrict scalars. -/
def coefficientRestrictedSquare : (ΓX₀ ⋙ Res₀) ⋙ HY₀ ≅ LX₀ ⋙ (ΓX₁ ⋙ Res₁) :=
  associator .. ≪≫ isoWhiskerLeft ΓX₀ (coefficientScalarSquare.{a,m} f) ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight
      (Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport.coefficientEvaluationComparisonValue.{max a u v r s,u,r,m} X R ⊤).symm Res₁ ≪≫
    associator ..

def CoefficientCoherence : Prop :=
  isoWhiskerRight (smallSectionsIdentity.{m} f) HY₀ ≪≫ coefficientRestrictedSquare.{a,m} f =
    coefficientCompositeSquare.{a,m} f ≪≫
      isoWhiskerLeft LX₀ (sectionsIdentity.{max a m} f)

end OriginalCoefficients

/-- Identify two successive carrier lifts with the single lift to their join. -/
def composedCoefficientLift {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) :
    liftSheafCoefficients.{a,u,r,m} R ⋙ liftSheafCoefficients.{b,u,r,max a m} R ≅
      liftSheafCoefficients.{max a b,u,r,m} R := by
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget R).preimageIso (PresheafOfModules.isoMk
      (fun V ↦ ?_) (fun {_ _} _ ↦ ?_))) ?_
  · let P := ((liftSheafCoefficients.{a,u,r,m} R ⋙ liftSheafCoefficients.{b,u,r,max a m} R).obj M).val.obj V
    let Q := ((liftSheafCoefficients.{max a b,u,r,m} R).obj M).val.obj V
    let e : (P : Type (max a b m)) ≃ₗ[R.obj.obj V] (Q : Type (max a b m)) :=
      { toFun := fun x ↦ ULift.up x.down.down
        invFun := fun x ↦ ULift.up (ULift.up x.down)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact e.toModuleIso
  · ext x
    rfl
  · intro M N g
    ext V x
    rfl

def composedCoefficientLiftOnComplexes {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) :
    (liftSheafCoefficients.{a,u,r,m} R).mapCochainComplexPlus ⋙
      (liftSheafCoefficients.{b,u,r,max a m} R).mapCochainComplexPlus ≅
      (liftSheafCoefficients.{max a b,u,r,m} R).mapCochainComplexPlus :=
  NatIso.ofComponents
    (fun I ↦ ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex (composedCoefficientLift.{a,b,m} R) (.up ℤ)).app I.obj))
    (fun g ↦ (CochainComplex.Plus.ι _).map_injective
      ((NatIso.mapHomologicalComplex (composedCoefficientLift.{a,b,m} R) (.up ℤ)).hom.naturality g.hom))

section CoefficientTransport

variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)

attribute [local instance] HasDerivedCategory.standard

set_option hygiene false in
local notation "A₀" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "A₁" => AmbientSheaves.{max a b v s} R
set_option hygiene false in
local notation "B₀" => AmbientSheaves.{max a u r} S
set_option hygiene false in
local notation "B₁" => AmbientSheaves.{max a b u r} S
set_option hygiene false in
local notation "D₀" => ambientDirectImage.{a} f
set_option hygiene false in
local notation "D₁" => ambientDirectImage.{max a b} f
set_option hygiene false in
local notation "ΓX₀" => globalSections.{max a v s} R
set_option hygiene false in
local notation "ΓX₁" => globalSections.{max a b v s} R
set_option hygiene false in
local notation "ΓY₀" => globalSections.{max a u r} S
set_option hygiene false in
local notation "ΓY₁" => globalSections.{max a b u r} S
set_option hygiene false in
local notation "Res₀" => scalarRestriction.{a} f
set_option hygiene false in
local notation "Res₁" => scalarRestriction.{max a b} f
set_option hygiene false in
local notation "JX" => liftSheafCoefficients.{max b u v r s,u,r,max a u v r s} R
set_option hygiene false in
local notation "JY" => liftSheafCoefficients.{max b u v r s,v,s,max a u v r s} S
set_option hygiene false in
local notation "HX" => ModuleCat.uliftFunctor.{max b u v r s,max a u v r s} (R.obj.obj (op ⊤))
set_option hygiene false in
local notation "HY" => ModuleCat.uliftFunctor.{max b u v r s,max a u v r s} (S.obj.obj (op ⊤))

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a u v r s}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a u v r s}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a u v r s}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a u v r s}]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a b u v r s}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a b u v r s}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a b u v r s}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a b u v r s}]
  [EnoughInjectives A₀] [EnoughInjectives A₁] [EnoughInjectives B₀] [EnoughInjectives B₁]
  [PreservesFiniteLimits JX] [PreservesFiniteColimits JX]
  [PreservesFiniteLimits JY] [PreservesFiniteColimits JY]

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport (coefficientEvaluationComparisonValue)
open Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients
  (coefficientLiftComparisonValue)

/-- The vertical functors lift the coefficient carriers over the original sites
and section rings. Each vertical map is fixed by the termwise map and the
derived units. -/
structure CoefficientTransportData (c₀ : SectionsData.{a} f) (c₁ : SectionsData.{max a b} f) where
  source : ExactDescent JX
  target : ExactDescent JY
  sourceModules : ExactDescent HX
  targetModules : ExactDescent HY
  sourceSections : UnitTransport ΓX₀ ΓX₁ JX HX
    (coefficientEvaluationComparisonValue.{max b u v r s,u,r,max a u v r s} X R ⊤).symm
    source sourceModules (ΓX₀).rightDerivedFunctorPlusUnit (ΓX₁).rightDerivedFunctorPlusUnit
  targetSections : UnitTransport ΓY₀ ΓY₁ JY HY
    (coefficientEvaluationComparisonValue.{max b u v r s,v,s,max a u v r s} Y S ⊤).symm
    target targetModules (ΓY₀).rightDerivedFunctorPlusUnit (ΓY₁).rightDerivedFunctorPlusUnit
  pushforward : UnitTransport D₀ D₁ JX JY
    (coefficientLiftComparisonValue.{max b u v r s,max a u v r s,u,v,r,s} f)
    source target (D₀).rightDerivedFunctorPlusUnit (D₁).rightDerivedFunctorPlusUnit
  restriction : UnitTransport Res₀ Res₁ HX HY (coefficientScalarSquare.{b,max a u v r s} f)
    sourceModules targetModules c₀.restriction.factors.inv c₁.restriction.factors.inv

variable {c₀ : SectionsData.{a} f} {c₁ : SectionsData.{max a b} f}

def CoefficientTransportData.restrictedIso (d : CoefficientTransportData.{a,b} f c₀ c₁) :=
  composeFunctorSquares d.sourceSections.iso d.restriction.iso

def CoefficientTransportData.iteratedIso (d : CoefficientTransportData.{a,b} f c₀ c₁) :=
  composeFunctorSquares d.pushforward.iso d.targetSections.iso

/-- Both derived paths extend the same ordinary termwise coefficient square. -/
def CoefficientTransportData.UnitCoherence (d : CoefficientTransportData.{a,b} f c₀ c₁) : Prop :=
  ∀ I : CochainComplex.Plus A₀,
    RespectsModelUnits (D₀ ⋙ ΓY₀) (D₁ ⋙ ΓY₁) JX HY
      (coefficientCompositeSquare.{b,max a u v r s} f) d.source d.targetModules
      (sectionsTermwiseUnit.{a} f c₀.restriction) (sectionsTermwiseUnit.{max a b} f c₁.restriction)
      (d.restrictedIso f) I ∧
    RespectsModelUnits (D₀ ⋙ ΓY₀) (D₁ ⋙ ΓY₁) JX HY
      (coefficientCompositeSquare.{b,max a u v r s} f) d.source d.targetModules
      (iteratedUnit D₀ ΓY₀) (iteratedUnit D₁ ΓY₁) (d.iteratedIso f) I

/-- The comparison is computed by termwise sections both on the injective
complex and on its acyclic coefficient lift. -/
def CoefficientTransportData.ModelCoherence (_d : CoefficientTransportData.{a,b} f c₀ c₁) : Prop :=
  ∀ I : CochainComplex.Plus A₀, (∀ k : ℤ, Injective (I.obj.X k)) →
    let I' := (JX).mapCochainComplexPlus.obj I
    c₀.ModelEquation f I ∧ c₁.ModelEquation f I' ∧
      IsIso ((sectionsTermwiseUnit.{max a b} f c₁.restriction).app I') ∧
      IsIso ((iteratedUnit D₁ ΓY₁).app I')

def CoefficientTransportData.DerivedCoherence (d : CoefficientTransportData.{a,b} f c₀ c₁) : Prop :=
  ∀ K : DerivedCategory.Plus A₀,
    d.targetModules.functor.map (c₀.iteratedIso.hom.app K) ≫ (d.iteratedIso f).hom.app K =
      (d.restrictedIso f).hom.app K ≫ c₁.iteratedIso.hom.app (d.source.functor.obj K)

def CoefficientTransportData.restrictedCohomologyIso
    (d : CoefficientTransportData.{a,b} f c₀ c₁) (n : ℤ) :
    ((ΓX₀).rightDerivedFunctorPlus ⋙ (DerivedCategory.Plus.homologyFunctor _ n ⋙ Res₀)) ⋙ HY ≅
      d.source.functor ⋙
        ((ΓX₁).rightDerivedFunctorPlus ⋙ (DerivedCategory.Plus.homologyFunctor _ n ⋙ Res₁)) :=
  isoWhiskerRight (isoWhiskerLeft _ (c₀.restriction.cohomology n).symm ≪≫ (associator ..).symm) HY ≪≫
    associator .. ≪≫ isoWhiskerLeft _ (d.targetModules.cohomology n).symm ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight (d.restrictedIso f) _ ≪≫
    associator .. ≪≫ isoWhiskerLeft _
      (associator .. ≪≫ isoWhiskerLeft _ (c₁.restriction.cohomology n))

def CoefficientTransportData.iteratedCohomologyIso
    (d : CoefficientTransportData.{a,b} f c₀ c₁) (n : ℤ) :
    (((D₀).rightDerivedFunctorPlus ⋙ (ΓY₀).rightDerivedFunctorPlus) ⋙
      DerivedCategory.Plus.homologyFunctor _ n) ⋙ HY ≅
    d.source.functor ⋙ (((D₁).rightDerivedFunctorPlus ⋙ (ΓY₁).rightDerivedFunctorPlus) ⋙
      DerivedCategory.Plus.homologyFunctor _ n) :=
  associator .. ≪≫ isoWhiskerLeft _ (d.targetModules.cohomology n).symm ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight (d.iteratedIso f) _ ≪≫ associator ..

/-- The cohomology square is formed from those same derived maps using the
canonical homology maps of the actual exact lifts and restriction. -/
def CoefficientTransportData.CohomologyCoherence
    (d : CoefficientTransportData.{a,b} f c₀ c₁) : Prop :=
  ∀ (K : DerivedCategory.Plus A₀) (n : ℤ),
    (HY).map ((c₀.cohomologyIso n).hom.app K) ≫ (d.iteratedCohomologyIso f n).hom.app K =
      (d.restrictedCohomologyIso f n).hom.app K ≫
        (c₁.cohomologyIso n).hom.app (d.source.functor.obj K)

end CoefficientTransport


section OriginalPlacement

variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)

attribute [local instance] HasDerivedCategory.standard

set_option hygiene false in
local notation "A₀" => AmbientSheaves.{max a m v s} R
set_option hygiene false in
local notation "A₁" => AmbientSheaves.{max a b m v s} R
set_option hygiene false in
local notation "B₀" => AmbientSheaves.{max a m u r} S
set_option hygiene false in
local notation "B₁" => AmbientSheaves.{max a b m u r} S
set_option hygiene false in
local notation "D₁" => ambientDirectImage.{max a b m} f
set_option hygiene false in
local notation "ΓX₁" => globalSections.{max a b m v s} R
set_option hygiene false in
local notation "ΓY₁" => globalSections.{max a b m u r} S
set_option hygiene false in
local notation "Res₁" => scalarRestriction.{max a b m} f
set_option hygiene false in
local notation "JX" => liftSheafCoefficients.{max b u v r s,u,r,max a m u v r s} R
set_option hygiene false in
local notation "JY" => liftSheafCoefficients.{max b u v r s,v,s,max a m u v r s} S
set_option hygiene false in
local notation "HY" => ModuleCat.uliftFunctor.{max b u v r s,max a m u v r s} (S.obj.obj (op ⊤))

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a m u v r s}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a m u v r s}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a m u v r s}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a m u v r s}]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a b m u v r s}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a b m u v r s}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a b m u v r s}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a b m u v r s}]
  [EnoughInjectives A₀] [EnoughInjectives A₁] [EnoughInjectives B₀] [EnoughInjectives B₁]
  [PreservesFiniteLimits JX] [PreservesFiniteColimits JX]
  [PreservesFiniteLimits JY] [PreservesFiniteColimits JY]

variable {c₀ : SectionsData.{max a m} f} {c₁ : SectionsData.{max a b m} f}

set_option hygiene false in
local notation "P₀" =>
  (coefficientLift.{a,m,u,v,r,s} f).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q
set_option hygiene false in
local notation "P₁" =>
  (coefficientLift.{max a b,m,u,v,r,s} f).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q

/-- The localized identification between a successive lift and the direct
placement of the original complex at the larger level. -/
def CoefficientTransportData.originalPlacementIso
    (d : CoefficientTransportData.{max a m,b} f c₀ c₁) :
    (P₀) ⋙ d.source.functor ≅ (P₁) :=
  associator .. ≪≫ isoWhiskerLeft _ d.source.factors ≪≫ (associator ..).symm ≪≫
    isoWhiskerRight (composedCoefficientLiftOnComplexes.{max a u v r s,max b u v r s,m,u,r} R) _

/-- Evaluate the same two comparisons on the original complex in both
placements, with its direct carrier lift at each level. -/
def CoefficientTransportData.OriginalComplexCoherence
    (d : CoefficientTransportData.{max a m,b} f c₀ c₁) : Prop :=
  ∀ K : CochainComplex.Plus (SheafOfModules.{m} R),
    let P := (P₀).obj K
    let z := (d.originalPlacementIso.{a,b,m} f).hom.app K
    let L := (ΓX₁).rightDerivedFunctorPlus ⋙ c₁.restriction.functor
    let M := (D₁).rightDerivedFunctorPlus ⋙ (ΓY₁).rightDerivedFunctorPlus
    (d.targetModules.functor.map ((c₀.onOriginalComplexes.{a,m}).hom.app K) ≫
        (d.iteratedIso f).hom.app P ≫ M.map z =
      (d.restrictedIso f).hom.app P ≫ L.map z ≫ (c₁.onOriginalComplexes.{max a b,m}).hom.app K) ∧
    ∀ n : ℤ,
      let Lh := (ΓX₁).rightDerivedFunctorPlus ⋙ (DerivedCategory.Plus.homologyFunctor _ n ⋙ Res₁)
      let Mh := M ⋙ DerivedCategory.Plus.homologyFunctor _ n
      (HY).map ((c₀.onOriginalCohomology.{a,m} n).hom.app K) ≫
          (d.iteratedCohomologyIso f n).hom.app P ≫ Mh.map z =
        (d.restrictedCohomologyIso f n).hom.app P ≫ Lh.map z ≫
          (c₁.onOriginalCohomology.{max a b,m} n).hom.app K

end OriginalPlacement

end AdvancedHomologicalAlgebra.OriginalDerivedSectionsTheory

namespace Specs.AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients
open AdvancedHomologicalAlgebra.OriginalDerivedSectionsTheory

def underivedCoherenceType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S),
    isoWhiskerRight (sectionsIdentity.{a} f) (targetScalars.{a} f) ≪≫ restrictedSquare.{a} f =
      compositeSquare.{a} f ≪≫ isoWhiskerLeft (transport.{max a v s} R) (liftedSectionsIdentity.{a} f)

def coefficientCoherenceType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S), CoefficientCoherence.{a,m,u,v,r,s} f


def coefficientExactType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S),
    letI := sectionHasSheafify.{max a m v r s,u} X
    letI := sectionWEqualsLocallyBijective.{max a m v r s,u} X
    ∀ K : ShortComplex (SheafOfModules.{m} R),
      GermLocallyShortExact R.obj (K.map (SheafOfModules.forget R)) ↔
        (K.map (coefficientLift.{a,m,u,v,r,s} f)).ShortExact


def derivedSectionsType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S),
    letI := sectionHasSheafify.{max a v r s,u} X
    letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
    letI := sectionHasSheafify.{max a u r s,v} Y
    letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
    ∃ (_ : EnoughInjectives (AmbientSheaves.{max a v s} R))
      (_ : EnoughInjectives (AmbientSheaves.{max a u r} S)),
      Nonempty (SectionsData.{a} f)

def transportType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S),
    letI := sectionHasSheafify.{max a v r s,u} X
    letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
    letI := sectionHasSheafify.{max a u r s,v} Y
    letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
    ∃ (_ : EnoughInjectives (AmbientSheaves.{max a v s} R))
      (_ : EnoughInjectives (AmbientSheaves.{max a u r} S))
      (_ : (transport.{max a v s} R).IsEquivalence) (c : SectionsData.{a} f),
      c.IsModelComparison f ∧ ∀ c' : liftedSectionsData.{a} f,
        ∃ d : SiteTransportData.{a} f c c', d.CohomologyCoherence f

/-- Coherence on the whole derived category of any adequate coefficient
level, with the actual carrier lift into a larger adequate level. -/
def coefficientTransportType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S),
    letI := sectionHasSheafify.{max a m v r s,u} X
    letI := sectionWEqualsLocallyBijective.{max a m v r s,u} X
    letI := sectionHasSheafify.{max a m u r s,v} Y
    letI := sectionWEqualsLocallyBijective.{max a m u r s,v} Y
    letI := sectionHasSheafify.{max a b m v r s,u} X
    letI := sectionWEqualsLocallyBijective.{max a b m v r s,u} X
    letI := sectionHasSheafify.{max a b m u r s,v} Y
    letI := sectionWEqualsLocallyBijective.{max a b m u r s,v} Y
    ∃ (_ : EnoughInjectives (AmbientSheaves.{max a m v s} R))
      (_ : EnoughInjectives (AmbientSheaves.{max a m u r} S))
      (_ : EnoughInjectives (AmbientSheaves.{max a b m v s} R))
      (_ : EnoughInjectives (AmbientSheaves.{max a b m u r} S))
      (_ : PreservesFiniteLimits (liftSheafCoefficients.{max b u v r s,u,r,max a m u v r s} R))
      (_ : PreservesFiniteColimits (liftSheafCoefficients.{max b u v r s,u,r,max a m u v r s} R))
      (_ : PreservesFiniteLimits (liftSheafCoefficients.{max b u v r s,v,s,max a m u v r s} S))
      (_ : PreservesFiniteColimits (liftSheafCoefficients.{max b u v r s,v,s,max a m u v r s} S))
      (c₀ : SectionsData.{max a m} f) (c₁ : SectionsData.{max a b m} f)
      (d : CoefficientTransportData.{max a m,b} f c₀ c₁),
        d.UnitCoherence f ∧ d.ModelCoherence f ∧ d.DerivedCoherence f ∧
          d.CohomologyCoherence f ∧ d.OriginalComplexCoherence.{a,b,m} f ∧
          c₀.SiteCoherence f ∧ c₁.SiteCoherence f


end Specs.AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients
