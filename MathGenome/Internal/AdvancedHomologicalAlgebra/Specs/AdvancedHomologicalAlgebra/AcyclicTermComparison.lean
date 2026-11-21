import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor

/-!
HA-R08, notes/002/advanced-homological-algebra.tex:1965–1999.
The ambient categories are abelian and F is additive (chapter convention,
1767–1775). Enough injectives/projectives is required only in the source.
Acyclicity is defined by the actual total comparison, without exactness of F.
The left side uses any of the exact left derived data constructed in HA-R07.
The natural-number derived objects below are H^n RF(X[0]) and H^(-n) LF(X[0]),
respectively; these are also the definitions in the following HA-R09.
-/
set_option linter.checkUnivs false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor

namespace Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

section Stalks
variable {A : Type u} [Category.{v} A] [Abelian A]

def plusStalkType := A → HomotopyCategory.Plus A
noncomputable def plusStalkValue : plusStalkType (A := A) :=
  fun X => (HomotopyCategory.Plus.singleFunctor A 0).obj X

def minusStalkType := A → KMinus A
noncomputable def minusStalkValue : minusStalkType (A := A) := fun X =>
  ⟨(HomotopyCategory.singleFunctor A 0).obj X, 0, by
    change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyLE 0
    infer_instance⟩
end Stalks

section Right
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]

def rightAcyclicType := ∀ (F : A ⥤ B) [F.Additive], A → Prop
noncomputable def rightAcyclicValue : rightAcyclicType (A := A) (B := B) :=
  fun F _ X => IsIso (F.rightDerivedFunctorPlusUnith.app (plusStalkValue X))

def rightDerivedObjectType := ∀ (F : A ⥤ B) [F.Additive], ℕ → A → B
noncomputable def rightDerivedObjectValue : rightDerivedObjectType (A := A) (B := B) :=
  fun F _ n X => (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj
    (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj (plusStalkValue X)))
end Right

section Left
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [(minus A).IsTriangulated] [(minus B).IsTriangulated]

def leftAcyclicType := ∀ (F : A ⥤ B) [F.Additive],
  ExactLeftData.{u, v, u', v', w, w'} F → A → Prop
noncomputable def leftAcyclicValue : leftAcyclicType (A := A) (B := B) :=
  fun _ _ R X => IsIso (R.counit.app (minusStalkValue X))

def leftDerivedObjectType := ∀ (F : A ⥤ B) [F.Additive],
  ExactLeftData.{u, v, u', v', w, w'} F → ℕ → A → B
noncomputable def leftDerivedObjectValue : leftDerivedObjectType (A := A) (B := B) :=
  fun _ _ R n X => (DerivedCategory.homologyFunctor B (-(n : ℤ))).obj
    (R.functor.obj ((QMinus A).obj (minusStalkValue X))).obj
end Left

/- Closed declaration types and values for the construction bindings. -/
def plusStalkDeclarationType :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A], plusStalkType (A := A)
noncomputable def plusStalkDeclarationValue : plusStalkDeclarationType := @plusStalkValue

def minusStalkDeclarationType :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A], minusStalkType (A := A)
noncomputable def minusStalkDeclarationValue : minusStalkDeclarationType := @minusStalkValue

def rightAcyclicDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A],
    rightAcyclicType (A := A) (B := B)
noncomputable def rightAcyclicDeclarationValue : rightAcyclicDeclarationType.{u, v, u', v', w, w'} :=
  fun {A} {B} _ _ _ _ _ _ _ => rightAcyclicValue (A := A) (B := B)

def rightDerivedObjectDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A],
    rightDerivedObjectType (A := A) (B := B)
noncomputable def rightDerivedObjectDeclarationValue : rightDerivedObjectDeclarationType.{u, v, u', v', w, w'} :=
  fun {A} {B} _ _ _ _ _ _ _ => rightDerivedObjectValue (A := A) (B := B)

def leftAcyclicDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [(minus A).IsTriangulated] [(minus B).IsTriangulated],
    leftAcyclicType (A := A) (B := B)
noncomputable def leftAcyclicDeclarationValue : leftAcyclicDeclarationType.{u, v, u', v', w, w'} :=
  fun {A} {B} _ _ _ _ _ _ _ _ => leftAcyclicValue (A := A) (B := B)

def leftDerivedObjectDeclarationType :=
  ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [(minus A).IsTriangulated] [(minus B).IsTriangulated],
    leftDerivedObjectType (A := A) (B := B)
noncomputable def leftDerivedObjectDeclarationValue : leftDerivedObjectDeclarationType.{u, v, u', v', w, w'} :=
  fun {A} {B} _ _ _ _ _ _ _ _ => leftDerivedObjectValue (A := A) (B := B)

/-- Full bounded-below comparison, for arbitrary additive F. -/
def rightComparisonType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (C : HomotopyCategory.Plus A),
    (∀ n : ℤ, rightAcyclicValue F (C.obj.as.X n)) →
      IsIso (F.rightDerivedFunctorPlusUnith.app C)

/-- Full bounded-above comparison; R is total left derived data from HA-R07. -/
def leftComparisonType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughProjectives A]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F)
      (C : KMinus A),
      (∀ n : ℤ, leftAcyclicValue F R (C.obj.as.X n)) → IsIso (R.counit.app C)

/-- Left exactness is used only for the object vanishing criterion. -/
def rightVanishingType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (X : A),
    rightAcyclicValue F X ↔ ∀ n : ℕ, IsZero (rightDerivedObjectValue F (n + 1) X)

/-- Right exactness is used only for the object vanishing criterion. -/
def leftVanishingType : Prop :=
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughProjectives A]
    (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated),
    letI := hA; letI := hB
    ∀ (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
      (R : ExactLeftData.{u, v, u', v', w, w'} F) (X : A),
      leftAcyclicValue F R X ↔ ∀ n : ℕ, IsZero (leftDerivedObjectValue F R (n + 1) X)

end Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
