import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedSectionsComposition
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GrothendieckEdges

/-! HA-H07, notes/002/advanced-homological-algebra.tex, lines 3768–3787 and 3793–3800.
The functors in the statement use the actual maps of structure sheaves.
Page zero of the row diagram denotes E₂, with indices (p,p+q).
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Functor

namespace AdvancedHomologicalAlgebra.LerayAndDegenerations
open SheafTheory HigherDirectImageLocalTheory DerivedSectionsTheory
open GrothendieckSpectralSequence GrothendieckEdges
open _root_.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y)
  (f : X ⟶ Y) (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)

local notation "D" => directImage R S f φ
local notation "ΓY" => globalSections S
local notation "Res" => scalarRestriction R S f φ

/-- Hypercohomology with its original global section-ring action. -/
abbrev hypercohomology (n : ℤ) : DerivedCategory.Plus (Modules R) ⥤
    ModuleCat.{u} (sectionRing R ⊤) :=
  (globalSections R).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor _ n

/-- A single sequence over the target section ring, together with its stalk
specialization and the natural identification of its abutment. -/
structure LerayData where
  package : Package D ΓY
  edges : ObjectEdges D ΓY package
  sections : SectionsDerivedData R S f φ

variable {R S f φ} (L : LerayData R S f φ)

/-- The canonical comparison from HA-H06, computed by sections on injective models. -/
abbrev LerayData.comparison (n : ℤ) :
    compositeValue D ΓY n ≅ hypercohomology R n ⋙ Res :=
  L.sections.cohomologyIso n

/-- The derived second page `H^p(Y, H^q(Rf_* K))`. -/
def LerayData.derivedSecondIso (p : ℕ) (q : ℤ) :
    sequence D ΓY L.package.row ⋙ pageEval 0 (p : ℤ) ((p : ℤ) + q) ≅
      (D).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor _ q ⋙
        sectionCohomology S ⊤ p :=
  L.package.secondIso p q

/-- The sheaf second page `H^p(Y, R^q f_* F)`. -/
def LerayData.sheafSecondIso (p q : ℕ) :
    objectSequence D ΓY L.package ⋙ pageEval 0 (p : ℤ) ((p : ℤ) + (q : ℤ)) ≅
      higherDirectImage R S f φ q ⋙ sectionCohomology S ⊤ p :=
  L.edges.objectCase.secondIso p q

def LerayData.derivedTargetIso (n : ℤ) :
    sequence D ΓY L.package.row ⋙ targetEval n ≅ hypercohomology R n ⋙ Res :=
  L.package.targetIso n ≪≫ L.comparison n

def LerayData.sheafTargetIso (n : ℕ) :
    objectSequence D ΓY L.package ⋙ targetEval (n : ℤ) ≅
      sectionCohomology R ⊤ n ⋙ Res :=
  isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (Modules R) 0) (L.derivedTargetIso n)

/-- The finite filtration transported to the scalar-restricted abutment.
The sheaf filtration is its evaluation on the degree-zero stalk. -/
def LerayData.filtration (K : DerivedCategory.Plus (Modules R)) (p n : ℤ) :
    Subobject (((hypercohomology R n) ⋙ Res).obj K) :=
  imageSubobject ((((sequence D ΓY L.package.row).obj K).inclusion p n) ≫
    (L.derivedTargetIso n).hom.app K)

def LerayData.rowEdge (n : ℕ) :
    D ⋙ sectionCohomology S ⊤ n ⟶ sectionCohomology R ⊤ n ⋙ Res :=
  derivedFirstEdge D ΓY L.package n ≫
    (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (Modules R) 0)
      (L.comparison (n : ℤ))).hom

def LerayData.columnEdge (n : ℕ) :
    sectionCohomology R ⊤ n ⋙ Res ⟶ higherDirectImage R S f φ n ⋙ ΓY :=
  (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (Modules R) 0)
    (L.comparison (n : ℤ))).inv ≫
    classicalColumn D ΓY (L.edges.truncation n) L.edges.degreeZero

/-- Both isomorphism assertions concern the components of the natural edges
of the very same sequence. The vanishing conditions are independent. -/
def GlobalStatement : Prop :=
  ∀ {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R),
    ∃ L : LerayData R S f φ,
      (∀ M : Modules R, (∀ q : ℕ, 0 < q →
        IsZero ((higherDirectImage R S f φ q).obj M)) →
          ∀ n : ℕ, IsIso ((L.rowEdge n).app M)) ∧
      (∀ M : Modules R, (∀ p q : ℕ, 0 < p →
        IsZero (((higherDirectImage R S f φ q ⋙ sectionCohomology S ⊤ p).obj M))) →
          ∀ n : ℕ, IsIso ((L.columnEdge n).app M))

end AdvancedHomologicalAlgebra.LerayAndDegenerations
