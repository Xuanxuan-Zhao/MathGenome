import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
HA-D02, notes/002/advanced-homological-algebra.tex:1455–1513.
The section assumes an arbitrary abelian category, unbounded integer cochain
complexes, and a universe containing the roofs. We use the canonical localization
whose morphism universe is enlarged to contain the object and morphism universes
of K(A). Thus no smallness or resolution hypothesis is imposed on A.

`W` is exactly the ordinary cohomology quasi-isomorphisms on the shared K(A).
Right fractions have shape X ← T → Y; left fractions have shape X → T ← Y.
Equality below is explicitly a common refinement in K(A), not equality of
cochain representatives. Both refinement maps are themselves quasi-isomorphisms.
The localization assertion and the unique functor factorization ensure this is
an actual categorical localization with the full universal property.
-/

set_option linter.checkUnivs false
universe v u v' u'
open CategoryTheory
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts

namespace Specs.AdvancedHomologicalAlgebra.DerivedFractions

abbrev W (A : Type u) [Category.{v} A] [Abelian A] : MorphismProperty (K A) :=
  HomotopyCategory.quasiIso A (ComplexShape.up ℤ)

noncomputable abbrev L (A : Type u) [Category.{v} A] [Abelian A] := (W A).Q

def rightCalculusType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], (W A).HasRightCalculusOfFractions

def leftCalculusType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], (W A).HasLeftCalculusOfFractions

/-- The constructed category, with its genuine category instance, is a localization. -/
def localizationType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], (L A).IsLocalization (W A)

/-- Every functor inverting quasi-isomorphisms has a unique factorization.
For the canonical localization this can be stated with strict equality. -/
def universalType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (E : Type u') [Category.{v'} E] (F : K A ⥤ E),
    (W A).IsInvertedBy F →
      ∃! G : (W A).Localization ⥤ E, L A ⋙ G = F

/-- Roof presentation, valid for any model of the localization. -/
def rightRoofType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (E : Type u') [Category.{v'} E] (J : K A ⥤ E) [J.IsLocalization (W A)]
    (X Y : K A) (f : J.obj X ⟶ J.obj Y),
    ∃ r : (W A).RightFraction X Y, f = r.map J (Localization.inverts J (W A))

/-- The dual roof presentation. -/
def leftRoofType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (E : Type u') [Category.{v'} E] (J : K A ⥤ E) [J.IsLocalization (W A)]
    (X Y : K A) (f : J.obj X ⟶ J.obj Y),
    ∃ r : (W A).LeftFraction X Y, f = r.map J (Localization.inverts J (W A))

/-- Two roofs agree exactly when both arrows agree after a common refinement. -/
def rightRoof_eq_iffType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (E : Type u') [Category.{v'} E] (J : K A ⥤ E) [J.IsLocalization (W A)]
    (X Y : K A) (r q : (W A).RightFraction X Y),
    r.map J (Localization.inverts J (W A)) = q.map J (Localization.inverts J (W A)) ↔
      ∃ (T : K A) (a : T ⟶ r.X') (b : T ⟶ q.X'),
        W A a ∧ W A b ∧ a ≫ r.s = b ≫ q.s ∧ a ≫ r.f = b ≫ q.f

/-- The same criterion in the dual orientation. -/
def leftRoof_eq_iffType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (E : Type u') [Category.{v'} E] (J : K A ⥤ E) [J.IsLocalization (W A)]
    (X Y : K A) (r q : (W A).LeftFraction X Y),
    r.map J (Localization.inverts J (W A)) = q.map J (Localization.inverts J (W A)) ↔
      ∃ (T : K A) (a : r.Y' ⟶ T) (b : q.Y' ⟶ T),
        W A a ∧ W A b ∧ r.s ≫ a = q.s ≫ b ∧ r.f ≫ a = q.f ≫ b

end Specs.AdvancedHomologicalAlgebra.DerivedFractions
