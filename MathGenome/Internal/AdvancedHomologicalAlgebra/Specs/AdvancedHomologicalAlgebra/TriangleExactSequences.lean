import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
HA-K06, notes/002/advanced-homological-algebra.tex:1402–1430. Cochain
conventions are at 107–109 and the closing sign -p is fixed at 1325–1328.

For every integer n, `LongExact` asserts exactness of the six consecutive
terms Fⁿ(X) → Fⁿ(Y) → Fⁿ(Z) → Fⁿ⁺¹(X) → Fⁿ⁺¹(Y) → Fⁿ⁺¹(Z).
Thus it asserts exactness at every position in the two-sided infinite sequence.
The connecting map is induced by the actual third arrow, with no sign change.

For coyoneda these terms are Hom(U,X[n]), Hom(U,Y[n]), Hom(U,Z[n]).
For yoneda on the opposite triangle they are Hom(Z,U[n]), Hom(Y,U[n]),
Hom(X,U[n]), in this reversed order. Shifting the target in this last
sequence is equivalently shifting the sources by the opposite integer.
For cohomology they are the ordinary Hⁿ(X), Hⁿ(Y), Hⁿ(Z), by the
HA-K01 shift sequence, whose nth functor is definitionally Hⁿ.
-/

set_option linter.checkUnivs false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Pretriangulated.Opposite
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.MappingCones
open Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory

namespace Specs.AdvancedHomologicalAlgebra.TriangleExactSequences

section Sequence
variable {C B : Type*} [Category* C] [HasShift C ℤ]
  [Category* B] [HasZeroMorphisms B] (F : C ⥤ B) [F.ShiftSequence ℤ]

/-- The connecting arrow uses the third triangle arrow and the fixed shift comparison. -/
noncomputable abbrev boundary (D : Triangle C) (n : ℤ) :=
  F.homologySequenceδ D n (n + 1) rfl

/-- All overlapping six-term windows of the infinite sequence are exact. -/
def LongExact (D : Triangle C) : Prop :=
  ∀ n : ℤ, (F.homologySequenceComposableArrows₅ D n (n + 1) rfl).Exact

/-- The three squares in each degree; together they give all squares of the long sequence. -/
def Natural {D E : Triangle C} (φ : D ⟶ E) : Prop :=
  ∀ n : ℤ,
    (F.shift n).map φ.hom₁ ≫ (F.shift n).map E.mor₁ =
      (F.shift n).map D.mor₁ ≫ (F.shift n).map φ.hom₂ ∧
    (F.shift n).map φ.hom₂ ≫ (F.shift n).map E.mor₂ =
      (F.shift n).map D.mor₂ ≫ (F.shift n).map φ.hom₃ ∧
    (F.shift n).map φ.hom₃ ≫ boundary F E n =
      boundary F D n ≫ (F.shift (n + 1)).map φ.hom₁
end Sequence

/-- Covariant representable Hom, with no abelian assumption on A. -/
def covariantHom_exactType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasZeroObject A]
    [HasBinaryBiproducts A] (D : Triangle (K A)), Distinguished D →
    ∀ U : K A, LongExact (preadditiveCoyoneda.obj (Opposite.op U)) D

/-- Contravariant representable Hom reverses the three terms and all arrows. -/
def contravariantHom_exactType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasZeroObject A]
    [HasBinaryBiproducts A] (D : Triangle (K A)), Distinguished D →
    ∀ U : K A, LongExact (preadditiveYoneda.obj U)
      ((triangleOpEquivalence (K A)).functor.obj (Opposite.op D))

/-- All degrees of ordinary cohomology, without boundedness assumptions. -/
def cohomology_exactType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (D : Triangle (K A)), Distinguished D → LongExact (H A 0) D

/-- Naturality for the maps obtained by postcomposition in Hom(U,-). -/
def covariantHom_naturalType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasZeroObject A]
    [HasBinaryBiproducts A] (D E : Triangle (K A)) (φ : D ⟶ E)
    (U : K A), Natural (preadditiveCoyoneda.obj (Opposite.op U)) φ

/-- Naturality for Hom(-,U); a triangle map induces the map in the reverse direction. -/
def contravariantHom_naturalType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasZeroObject A]
    [HasBinaryBiproducts A] (D E : Triangle (K A)) (φ : D ⟶ E)
    (U : K A), Natural (preadditiveYoneda.obj U)
      ((triangleOpEquivalence (K A)).functor.map φ.op)

/-- Naturality for all three arrows of the cohomology long exact sequence. -/
def cohomology_naturalType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (D E : Triangle (K A)) (φ : D ⟶ E), Natural (H A 0) φ

/-- Explicit Hom(U,-) boundary, including the actual closing arrow. -/
def covariantHom_boundaryType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasZeroObject A]
    [HasBinaryBiproducts A] (D : Triangle (K A)) (U : K A) (n : ℤ)
    (x : U ⟶ D.obj₃⟦n⟧),
    boundary (preadditiveCoyoneda.obj (Opposite.op U)) D n x =
      x ≫ D.mor₃⟦n⟧' ≫
        (shiftFunctorAdd' (K A) 1 n (n + 1) (add_comm 1 n)).inv.app D.obj₁

/-- Explicit reversed Hom(-,U) boundary Hom(X,U[n]) → Hom(Z,U[n+1]). -/
def contravariantHom_boundaryType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasZeroObject A]
    [HasBinaryBiproducts A] (D : Triangle (K A)) (U : K A) (n : ℤ)
    (x : D.obj₁ ⟶ U⟦n⟧),
    boundary (preadditiveYoneda.obj U)
      ((triangleOpEquivalence (K A)).functor.obj (Opposite.op D)) n x =
      D.mor₃ ≫ x⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (K A) n 1 (n + 1) rfl).inv.app U

/-- Cohomology boundary Hⁿ(Z) → Hⁿ⁺¹(X) induced by the closing arrow. -/
def cohomology_boundaryType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (D : Triangle (K A)) (n : ℤ),
    boundary (H A 0) D n = (H A n).map D.mor₃ ≫
      (cohomologyShiftHomotopyValue A 1 n).hom.app D.obj₁

/-- On the source's cone row, the boundary is induced by -p, not by p. -/
def cohomology_cone_signType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (X Y : CochainComplex A ℤ) (f : X ⟶ Y) (n : ℤ),
    boundary (H A 0) (coneTriangle f) n =
      -((H A n).map ((Q A).map (projectionToShift f) ≫
          ((Q A).commShiftIso (1 : ℤ)).hom.app X) ≫
        (cohomologyShiftHomotopyValue A 1 n).hom.app ((Q A).obj X))

end Specs.AdvancedHomologicalAlgebra.TriangleExactSequences
