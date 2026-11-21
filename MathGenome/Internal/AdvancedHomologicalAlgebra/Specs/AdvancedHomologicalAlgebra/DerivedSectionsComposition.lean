import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExactFunctorLocalization
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! HA-H06, source 3733–3766; ringed-space and coefficient conventions 3515–3523.
The scalar functor is restriction along the actual global structure-ring map.
Its derived functor is identified with termwise restriction, including on
cohomology. No acyclicity or composition comparison is assumed here. -/
noncomputable section
set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.HigherDirectImageLocalTheory
universe u

namespace AdvancedHomologicalAlgebra.DerivedSectionsTheory

abbrev globalSections {X : TopCat.{u}} (R : RingSheaf X) :=
  SheafOfModules.evaluation.{u} R (op (⊤ : Opens X))

/-- The ring map S(Y) → R(X), including the given structure-sheaf morphism. -/
def globalRingMap {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y)
    (f : X ⟶ Y) (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R) :
    sectionRing S ⊤ →+* sectionRing R ⊤ :=
  (φ.hom.app (op ⊤)).hom

abbrev scalarRestriction {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y)
    (f : X ⟶ Y) (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R) :=
  ModuleCat.restrictScalars.{u} (globalRingMap R S f φ)

section
variable {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
  (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)

local notation "D" => directImage R S f φ
local notation "ΓX" => globalSections R
local notation "ΓY" => globalSections S
local notation "Res" => scalarRestriction R S f φ

/-- The sections of the pushforward are the same sections on the inverse
image of the whole space, with the scalar action restricted by the ring map. -/
def sectionsIdentity : D ⋙ ΓY ≅ ΓX ⋙ Res :=
  Iso.refl _

attribute [local instance] HasDerivedCategory.standard

private abbrev SectionModules {T : TopCat.{u}} (A : RingSheaf T) :=
  ModuleCat.{u} (sectionRing A ⊤)

local notation "RX" => SectionModules R
local notation "SY" => SectionModules S
local notation "RC" => (D ⋙ ΓY).rightDerivedFunctorPlus
local notation "RGX" => (ΓX).rightDerivedFunctorPlus
local notation "ιX" => DerivedCategory.Plus.ι (C := RX)
local notation "ιY" => DerivedCategory.Plus.ι (C := SY)

/-- The bounded exact restriction is identified with termwise scalar
restriction by the factorization of the actual localization. Its comparison
on cohomology is the map induced by exact restriction on cycles and boundaries. -/
structure ScalarRestrictionData where
  termwise : (Res).rightDerivedFunctorPlus ⋙ ιY ≅ ιX ⋙ (Res).mapDerivedCategory
  termwise_on_complex : ∀ K : CochainComplex.Plus RX,
    (ιY).map ((Res).rightDerivedFunctorPlusUnit.app K) ≫
      termwise.hom.app (DerivedCategory.Plus.Q.obj K) =
      (Res).mapDerivedCategoryFactors.inv.app K.obj
  homology (n : ℤ) : (Res).mapDerivedCategory ⋙ DerivedCategory.homologyFunctor SY n ≅
    DerivedCategory.homologyFunctor RX n ⋙ Res
  homology_on_complex : ∀ (n : ℤ) (K : CochainComplex RX ℤ),
    (homology n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor SY n).map
        ((Res).mapDerivedCategoryFactors.hom.app K) ≫
      (DerivedCategory.homologyFunctorFactors SY n).hom.app
        (((Res).mapHomologicalComplex (.up ℤ)).obj K) ≫
      ((K.sc n).mapHomologyIso Res).hom ≫
      (Res).map ((DerivedCategory.homologyFunctorFactors RX n).inv.app K)

/-- The comparison for the derived composite is induced by the actual
underived sections identity on each bounded-below injective model. The
target after inclusion in the unbounded category is the actual termwise
scalar restriction of the derived sections on X. -/
structure SectionsDerivedData where
  restriction : ScalarRestrictionData R S f φ
  comparison : RC ≅ RGX ⋙ (Res).rightDerivedFunctorPlus
  on_injective : ∀ (I : CochainComplex.Plus (Modules R)),
    (∀ j : ℤ, Injective (I.obj.X j)) →
    let K := ((ΓX).mapCochainComplexPlus.obj I).obj
    let A := DerivedCategory.Plus.Q.obj I
    (ιY).map ((D ⋙ ΓY).rightDerivedFunctorPlusUnit.app I) ≫
      (ιY).map (comparison.hom.app A) ≫ restriction.termwise.hom.app ((RGX).obj A) =
    DerivedCategory.Q.map
      ((mapHomologicalComplexCompIso (sectionsIdentity R S f φ).symm (.up ℤ)).inv.app I.obj) ≫
      (Res).mapDerivedCategoryFactors.inv.app K ≫
      (Res).mapDerivedCategory.map ((ιX).map ((ΓX).rightDerivedFunctorPlusUnit.app I))
  composition_isIso : IsIso
    (Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue D ΓY)

variable {R S f φ}

/-- The forward comparison on the entire bounded-below derived category. -/
def SectionsDerivedData.iteratedIso (c : SectionsDerivedData R S f φ) :
    RGX ⋙ (Res).rightDerivedFunctorPlus ≅
      (D).rightDerivedFunctorPlus ⋙ (ΓY).rightDerivedFunctorPlus := by
  letI := c.composition_isIso
  exact c.comparison.symm ≪≫
    asIso (Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue D ΓY)

/-- The same forward comparison in the termwise restriction coordinates. -/
def SectionsDerivedData.termwiseIso (c : SectionsDerivedData R S f φ) :
    RGX ⋙ ιX ⋙ (Res).mapDerivedCategory ≅
      ((D).rightDerivedFunctorPlus ⋙ (ΓY).rightDerivedFunctorPlus) ⋙ ιY :=
  (isoWhiskerLeft RGX c.restriction.termwise).symm ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight (c.iteratedIso) ιY

/-- Its composite-to-restricted form on cohomology. Both the exact
restriction comparison and the comparison of derived sections above are
used in the indicated degree. -/
def SectionsDerivedData.cohomologyIso (c : SectionsDerivedData R S f φ) (n : ℤ) :
    RC ⋙ DerivedCategory.Plus.homologyFunctor SY n ≅
      RGX ⋙ DerivedCategory.Plus.homologyFunctor RX n ⋙ Res :=
  isoWhiskerRight c.comparison (DerivedCategory.Plus.homologyFunctor SY n) ≪≫
    associator _ _ _ ≪≫ isoWhiskerLeft RGX (
      (associator _ _ _).symm ≪≫
      isoWhiskerRight c.restriction.termwise (DerivedCategory.homologyFunctor SY n) ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft ιX (c.restriction.homology n) ≪≫
      (associator _ _ _).symm)

end

end AdvancedHomologicalAlgebra.DerivedSectionsTheory

namespace Specs.AdvancedHomologicalAlgebra.DerivedSectionsComposition
open AdvancedHomologicalAlgebra.DerivedSectionsTheory

/-- The local presheaf and sheafification, with the original varying scalar rings. -/
def localDescriptionType : Prop :=
  Specs.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription.localDescriptionType.{u}

/-- Section acyclicity on every open of the target. -/
def injectivePushforwardAcyclicType : Prop :=
  Specs.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription.injectivePushforwardAcyclicType.{u}

/-- Both left-exactness hypotheses needed to apply HA-R12. -/
def leftExactType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R),
    PreservesFiniteLimits (directImage R S f φ) ∧
    PreservesFiniteLimits (globalSections S)

/-- The actual underived identification, with its coefficient functor. -/
def sectionsIdentityType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R),
    Nonempty (directImage R S f φ ⋙ globalSections S ≅
      globalSections R ⋙ scalarRestriction R S f φ)

/-- The section-acyclicity hypothesis of HA-R12, in its actual comparison form. -/
def compositionHypothesisType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R),
    letI := HasDerivedCategory.standard (Modules S)
    letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing S ⊤))
    ∀ I : Modules R, Injective I →
      AcyclicTermComparison.rightAcyclicValue (globalSections S) ((directImage R S f φ).obj I)

/-- Exact restriction, with its normalized termwise and cohomology comparisons. -/
def exactRestrictionType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R),
    letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R ⊤))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing S ⊤))
    PreservesFiniteLimits (scalarRestriction R S f φ) ∧
    PreservesFiniteColimits (scalarRestriction R S f φ) ∧
    Nonempty (ScalarRestrictionData R S f φ)

/-- One normalized natural comparison of derived functors, on all of D⁺.
Its forward, termwise, and cohomology forms are defined from this same data. -/
def derivedCompositionType : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R),
    letI := HasDerivedCategory.standard (Modules R)
    letI := HasDerivedCategory.standard (Modules S)
    letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R ⊤))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing S ⊤))
    Nonempty (SectionsDerivedData R S f φ)

end Specs.AdvancedHomologicalAlgebra.DerivedSectionsComposition
