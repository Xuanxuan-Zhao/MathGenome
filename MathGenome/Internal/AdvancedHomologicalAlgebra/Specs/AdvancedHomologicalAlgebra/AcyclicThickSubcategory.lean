import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
HA-D01, notes/002/advanced-homological-algebra.tex:1433–1454.
The chapter assumes an arbitrary abelian category. Complexes are unbounded
cochain complexes, with the signed integer shifts of HA-K01. Acyclicity means
vanishing of ordinary cohomology in every integer degree, not contractibility.
The cone class below uses exactly the isomorphism-closed cone rows of HA-K05,
whose closing arrow is -p. No localization or choice of representatives is assumed.
-/

set_option linter.checkUnivs false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory

namespace Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory

/-- The full subcategory cut out by vanishing of every ordinary cohomology object. -/
def acyclicObjects (A : Type u) [Category.{v} A] [Abelian A] : ObjectProperty (K A) :=
  fun X => ∀ n : ℤ, IsZero ((H A n).obj X)

/-- Cone membership for maps of the homotopy category, using the source triangles. -/
def coneClass (A : Type u) [Category.{v} A] [Abelian A] : MorphismProperty (K A) :=
  fun X Y f => ∃ (Z : K A) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
    Distinguished (Triangle.mk f g h) ∧ acyclicObjects A Z

def acyclicSubcategoryType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], ObjectProperty (K A)
def acyclicSubcategoryValue : acyclicSubcategoryType := acyclicObjects

def coneClassType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], MorphismProperty (K A)
def coneClassValue : coneClassType := coneClass

/-- The objects above really are the acyclic complexes modulo homotopy. -/
def acyclic_quotient_iffType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (X : CochainComplex A ℤ),
    acyclicObjects A ((Q A).obj X) ↔ X.Acyclic

/-- Triangulated, strictly full, and closed under retracts: the thick conclusion.
`IsTriangulated` includes zero objects, all integer shifts and extension closure,
and equips the full subcategory with the inherited triangulated structure. -/
def thickType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A],
    (acyclicObjects A).IsTriangulated ∧
    (acyclicObjects A).IsClosedUnderIsomorphisms ∧
    (acyclicObjects A).IsStableUnderRetracts

/-- Closure under every signed integer shift. -/
def shift_closedType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (X : K A) (m : ℤ),
    acyclicObjects A X → acyclicObjects A (X⟦m⟧)

/-- Closure for the actual distinguished triangles of HA-K05. -/
def cone_closedType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (D : Triangle (K A)),
    Distinguished D → acyclicObjects A D.obj₁ → acyclicObjects A D.obj₂ →
      acyclicObjects A D.obj₃

/-- In particular this holds for the source mapping cone of every cochain map. -/
def mappingCone_closedType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
    X.Acyclic → Y.Acyclic → (MappingCones.coneComplex f).Acyclic

/-- The cone class on K(A) is exactly the maps inducing isomorphisms on H^n. -/
def coneClass_eq_quasiIsoType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A],
    coneClass A = HomotopyCategory.quasiIso A (ComplexShape.up ℤ)

/-- The cochain representative form of the same cone criterion. -/
def cone_criterionType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
    QuasiIso f ↔ (MappingCones.coneComplex f).Acyclic

/-- All three implications of two-out-of-three, for maps in K(A). -/
def two_out_of_threeType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A],
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty

end Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory
