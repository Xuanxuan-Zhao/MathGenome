import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
HA-D07, notes/002/advanced-homological-algebra.tex:1679–1713.
We use the unbounded derived category and ordinary cohomology of HA-D03.
The abelian and localization-universe conventions are at 1433–1438;
cochain shifts are K[m]^i = K^(i+m), as at 107–109.
`HasDerivedCategory` chooses a localization universe; HA-D03 supplies such a
choice for every abelian category. There are no boundedness or injectivity
hypotheses. The heart is the full subcategory of the intersection of the two
cohomological aisles. The equivalence below specifies both functors exactly,
so its unit and counit identify the inverse with ordinary H^0.
-/

set_option linter.checkUnivs false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open Specs.AdvancedHomologicalAlgebra.DerivedCategory

namespace Specs.AdvancedHomologicalAlgebra.StandardHeart

noncomputable abbrev standardT (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : TStructure (D A) :=
  _root_.DerivedCategory.TStructure.t

abbrev heart (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : ObjectProperty (D A) := (standardT A).heart

abbrev Heart (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] := (heart A).FullSubcategory

noncomputable abbrev stalk (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : A ⥤ D A := _root_.DerivedCategory.singleFunctor A 0

/-- The actual stalk embedding restricted to the heart. -/
noncomputable def toHeart (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : A ⥤ Heart A :=
  (heart A).lift (stalk A) (fun _X =>
    ((standardT A).mem_heart_iff _).mpr ⟨inferInstance, inferInstance⟩)

/-- Ordinary degree-zero cohomology, restricted along the full inclusion. -/
noncomputable abbrev heartH0 (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : Heart A ⥤ A := (heart A).ι ⋙ HD A 0

def tStructureType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], TStructure (D A)
noncomputable def tStructureValue : tStructureType := standardT

/-- All translated aisles, in particular the two aisles at zero in the source. -/
def cohomologicalAislesType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (n : ℤ) (X : D A),
    ((standardT A).le n X ↔ ∀ i : ℤ, n < i → IsZero ((HD A i).obj X)) ∧
    ((standardT A).ge n X ↔ ∀ i : ℤ, i < n → IsZero ((HD A i).obj X))

def heartDescriptionType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : D A), heart A X ↔
      (∀ i : ℤ, 0 < i → IsZero ((HD A i).obj X)) ∧
      (∀ i : ℤ, i < 0 → IsZero ((HD A i).obj X))

def stalkType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], A ⥤ D A
noncomputable def stalkValue : stalkType := stalk

def fullyFaithfulType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A],
    Nonempty ((stalk A).FullyFaithful)

def heartEquivalenceType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A],
    ∃ e : A ≌ Heart A, e.functor = toHeart A ∧ e.inverse = heartH0 A

/-- Hom_D(X[0],Y[m]) is the zero group for every negative integer m. -/
def negativeHomsType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X Y : A) (m : ℤ), m < 0 →
      ∀ f : (stalk A).obj X ⟶ ((stalk A).obj Y)⟦m⟧, f = 0

end Specs.AdvancedHomologicalAlgebra.StandardHeart
