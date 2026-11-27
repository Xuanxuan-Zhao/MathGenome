import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone
import Mathlib.CategoryTheory.Triangulated.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace Specs.DerivedFormalization.DG.HomotopyTriangulation

open _root_.DerivedFormalization
open Basic (h0CategoryStruct)
open HomComplex (homotopyCategory dgModuleCategory homotopyClass gradedHom component HomotopyEquation)
open ShiftCone (shift shiftMap cone coneInclusion coneProjection ConeAcyclicCriterion
  ObjectwiseShortExact ConnectingMap GradedSplit)

/-- A cone triangle uses the negative of the quotient map as its third arrow. -/
def IsConeTriangle {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    [Category (homotopyCategory A)] [HasShift (homotopyCategory A) ℤ]
    {M N : RightDGModuleModel A} (f : M ⟶ N) (T : Triangle (homotopyCategory A)) : Prop :=
  T.obj₁ = M ∧ T.obj₂ = N ∧ T.obj₃ = cone f ∧
    HEq T.mor₁ (homotopyClass f) ∧ HEq T.mor₂ (homotopyClass (coneInclusion f)) ∧
    HEq T.mor₃ (-homotopyClass (coneProjection f))

/-- A specified right-linear homotopy of a square gives the comparison of its cones. -/
def ConeSquareComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N M' N' : RightDGModuleModel A}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : gradedHom M N' (-1)), HomotopyEquation (f ≫ b) (a ≫ g) h →
    ∃ c : cone f ⟶ cone g,
      coneInclusion f ≫ c = b ≫ coneInclusion g ∧
      c ≫ coneProjection g = coneProjection f ≫ shiftMap 1 a ∧
      ∀ (o : A.Obj) (i : ℤ) (p : ShiftCone.coneTerm M N o i),
        (c.app o).f i p =
          ((b.app o).f i p.1 + component h o (i+1) i (by omega) p.2,
            (a.app o).f (i+1) p.2)

/-- The shift and triangulation on the actual degree-zero cohomology category of dg modules. -/
def Triangulation : Prop :=
  GradedSplit.{u,v,w} ∧ ObjectwiseShortExact.{u,v,w} ∧
  ConnectingMap.{u,v,w} ∧ ConeAcyclicCriterion.{u,v,w} ∧
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    ∃ C : Category.{max v w} (homotopyCategory A),
      C.toCategoryStruct = h0CategoryStruct (dgModuleCategory A) ∧
      letI := C
      ∃ (S : HasShift (homotopyCategory A) ℤ) (P : Preadditive (homotopyCategory A)),
        letI := S
        letI := P
        ∃ (Z : HasZeroObject (homotopyCategory A))
          (L : ∀ n : ℤ, Functor.Additive (shiftFunctor (homotopyCategory A) n)),
          letI := Z
          letI := L
          ∃ T : Pretriangulated (homotopyCategory A),
            letI := T
            IsTriangulated (homotopyCategory A) ∧
            (∀ (M : RightDGModuleModel A) (s : ℤ),
              (shiftFunctor (homotopyCategory A) s).obj M = shift M s) ∧
            (∀ {M N : RightDGModuleModel A} (s : ℤ) (f : M ⟶ N),
              ∃ g : @Quiver.Hom (homotopyCategory A) C.toCategoryStruct.toQuiver M N,
                HEq g (homotopyClass f) ∧
                HEq ((shiftFunctor (homotopyCategory A) s).map g)
                  (homotopyClass (shiftMap s f))) ∧
            (∀ {M N : RightDGModuleModel A} (f g : M ⟶ N),
              homotopyClass f = homotopyClass g →
              ∃ (X Y : Triangle (homotopyCategory A)), IsConeTriangle f X ∧ IsConeTriangle g Y ∧
                ∃ e : X ≅ Y,
                  HEq e.hom.hom₁ (@CategoryStruct.id (homotopyCategory A) C.toCategoryStruct M) ∧
                  HEq e.hom.hom₂ (@CategoryStruct.id (homotopyCategory A) C.toCategoryStruct N)) ∧
            (∀ (X : Triangle (homotopyCategory A)),
              X ∈ distTriang (homotopyCategory A) ↔
                ∃ (M N : RightDGModuleModel A) (f : M ⟶ N)
                  (Y : Triangle (homotopyCategory A)), IsConeTriangle f Y ∧ Nonempty (X ≅ Y))

end Specs.DerivedFormalization.DG.HomotopyTriangulation
