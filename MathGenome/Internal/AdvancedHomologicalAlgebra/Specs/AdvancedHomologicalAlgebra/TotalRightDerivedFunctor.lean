import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
HA-R06, source lines 1910–1937 and the shift assertion at 1960–1964.
The chapter conventions (1767–1775) require additive functors between abelian
categories; enough injectives is required only in the source. The full categories
D⁺ and K⁺ are the shared ones of HA-D06 and HA-R05. Their bounds are on
cohomology and on terms respectively. No left exactness hypothesis is imposed.
The library construction is fixed as the canonical value, and the propositions
below separately require its universal property, exactness, computation for
EVERY replacement, and the actions on transformations and shifts.
-/
set_option linter.checkUnivs false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty

namespace Specs.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor

section
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]

/-- The total right derived functor on the actual bounded below categories. -/
def rightFunctorType := ∀ (F : A ⥤ B) [F.Additive],
  _root_.DerivedCategory.Plus A ⥤ _root_.DerivedCategory.Plus B
noncomputable def rightFunctorValue : rightFunctorType (A := A) (B := B) :=
  fun F _ => F.rightDerivedFunctorPlus

/-- The comparison is from Q_B F_K, in the direction specified in HA-R05. -/
def unitType := ∀ (F : A ⥤ B) [F.Additive],
  plusUValue F ⟶ _root_.DerivedCategory.Plus.Qh ⋙ rightFunctorValue F
noncomputable def unitValue : unitType (A := A) (B := B) :=
  fun F _ => F.rightDerivedFunctorPlusUnith

/-- The map induced by a natural transformation of additive functors. -/
def derivedMapType := ∀ (F G : A ⥤ B) [F.Additive] [G.Additive],
  (F ⟶ G) → (rightFunctorValue F ⟶ rightFunctorValue G)
noncomputable def derivedMapValue : derivedMapType (A := A) (B := B) :=
  fun _ _ _ _ τ => τ.rightDerivedFunctorPlus
end

/-- Use the canonical termwise and quotient shift structures on U. -/
noncomputable local instance plusUCommShift
    {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] : (plusUValue F).CommShift ℤ :=
  inferInstanceAs ((F.mapHomotopyCategoryPlus ⋙ _root_.DerivedCategory.Plus.Qh).CommShift ℤ)

/-- Closed types for binding the construction declarations. -/
def rightFunctorDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A],
    rightFunctorType (A := A) (B := B)

def unitDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A],
    unitType (A := A) (B := B)

def derivedMapDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A],
    derivedMapType (A := A) (B := B)

/-- The comparison induces a bijection for every functor H, without any
additivity, exactness, or shift restriction on H. -/
def universalType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (H : _root_.DerivedCategory.Plus A ⥤
      _root_.DerivedCategory.Plus B),
    Function.Bijective (fun α : rightFunctorValue F ⟶ H =>
      unitValue F ≫ whiskerLeft _root_.DerivedCategory.Plus.Qh α)

/-- Exactness means a coherent commutation with shifts and preservation of
all distinguished triangles for that commutation. -/
def exactType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive],
    ∃ c : (rightFunctorValue F).CommShift ℤ, letI := c;
      (rightFunctorValue F).IsTriangulated ∧ NatTrans.CommShift (unitValue F) ℤ

/-- On every bounded below termwise injective model the comparison is invertible. -/
def modelComparisonType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (I : HomotopyCategory.Plus A),
    (∀ n : ℤ, Injective (I.obj.as.X n)) → IsIso ((unitValue F).app I)

/-- Computation on EVERY quasi-isomorphism to a termwise injective bounded below
complex, hence in particular on every termwise monic HA-R01 replacement.
The equation identifies the comparison with the actual termwise image F(f).
The right-hand object is Q_B(F(I)), not an unspecified isomorphic model. -/
def computesReplacementType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (X I : CochainComplex.Plus A) (f : X ⟶ I),
    QuasiIso f.hom → (∀ n : ℤ, Injective (I.obj.X n)) →
    ∃ e : (rightFunctorValue F).obj (_root_.DerivedCategory.Plus.Q.obj X) ≅
      _root_.DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I),
      F.rightDerivedFunctorPlusUnit.app X ≫ e.hom =
        _root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f)

/-- The induced map is compatible with the universal comparison. -/
def derivedMapComparisonType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F G : A ⥤ B) [F.Additive] [G.Additive] (τ : F ⟶ G),
    unitValue F ≫ whiskerLeft _root_.DerivedCategory.Plus.Qh (derivedMapValue F G τ) =
      plusUMapValue F G τ ≫ unitValue G

/-- Using the SAME model I for both functors, the derived transformation is
exactly the termwise transformation under the two comparison isomorphisms. -/
def derivedMapModelType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F G : A ⥤ B) [F.Additive] [G.Additive] (τ : F ⟶ G)
    (I : CochainComplex.Plus A), (∀ n : ℤ, Injective (I.obj.X n)) →
    ∃ (eF : _root_.DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I) ≅
        (rightFunctorValue F).obj (_root_.DerivedCategory.Plus.Q.obj I))
      (eG : _root_.DerivedCategory.Plus.Q.obj (G.mapCochainComplexPlus.obj I) ≅
        (rightFunctorValue G).obj (_root_.DerivedCategory.Plus.Q.obj I)),
      eF.hom = F.rightDerivedFunctorPlusUnit.app I ∧
      eG.hom = G.rightDerivedFunctorPlusUnit.app I ∧
      (derivedMapValue F G τ).app (_root_.DerivedCategory.Plus.Q.obj I) =
        eF.inv ≫ _root_.DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app I) ≫ eG.hom

/-- The cochain comparison as well as the homotopy comparison commutes with
all shifts, with a single coherent exact structure on RF. -/
def shiftCompatibilityType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive],
    ∃ c : (rightFunctorValue F).CommShift ℤ, letI := c;
      (rightFunctorValue F).IsTriangulated ∧
      NatTrans.CommShift (unitValue F) ℤ ∧
      NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ

end Specs.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor
