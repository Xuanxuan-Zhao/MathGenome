import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Orthogonality

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs.StandardGroups

universe u

namespace LinearAlgebraicGroups.Specs.SmoothDiagonalKernel

noncomputable section

variable {k : Type u} [Field k]

/-- The matrix of a test-algebra point in the given realization of the general linear group. -/
abbrev matrixPoint {n : ℕ} {G H : GroupScheme k} (j : G ⟶ H)
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Unipotent.Index.{u} n))
    (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj G).obj R) :
    Matrix.GeneralLinearGroup (Unipotent.Index.{u} n) R :=
  (e.hom.app R) (((groupPointsFunctor k).map j).app R x)

/-- A scheme-theoretic triangular realization, including its behavior on nonreduced rings. -/
def IsUpperTriangular {n : ℕ} {G H : GroupScheme k} (j : G ⟶ H)
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Unipotent.Index.{u} n)) :
    Prop :=
  ∀ (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj G).obj R),
    (matrixPoint j e R x).val.IsUpperTriangular

/-- The diagonal map is characterized by the diagonal matrix entries on every test algebra. -/
def IsDiagonalMorphism {n : ℕ} {G H T : GroupScheme k} (j : G ⟶ H)
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Unipotent.Index.{u} n))
    (t : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (Unipotent.Index.{u} n))
    (d : G ⟶ T) : Prop :=
  ∀ (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj G).obj R)
    (i : Unipotent.Index.{u} n),
    ((t.hom.app R (((groupPointsFunctor k).map d).app R x) i : Rˣ) : R) =
      (matrixPoint j e R x).val i i

/-- An affine algebraic group is a torus when its coordinate Hopf algebra defines a torus. -/
def IsTorusGroup (D : AffineAlgebraicGroup k) : Prop :=
  ∃ A : HopfAlgebraCategory k, Nonempty (specGroup A ≅ D.val) ∧ CharacterDescent.IsTorus A

/-- The geometric diagonal-kernel assertion of Result B12. The closed triangular subgroup
is given by its closed inclusion into the matrix group and its upper-triangular functor
of points. The two ambient groups are specified by their representing functors. -/
def SmoothDiagonalKernel : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (G H T : AffineAlgebraicGroup k)
    (j : G.val ⟶ H.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Unipotent.Index.{u} n))
    (t : (groupPointsFunctor k).obj T.val ≅ multiplicativePowerPoints k (Unipotent.Index.{u} n)),
    IsClosedImmersion j.hom.hom.left → IsUpperTriangular j e →
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∃ (d : G.val ⟶ T.val), IsDiagonalMorphism j e t d ∧
      ∃ (D : AffineAlgebraicGroup k) (p : G.val ⟶ D.val) (i : D.val ⟶ T.val)
        (U : ClosedSubgroup G.val),
        IsImageFactorization d p i ∧ IsCanonicalImage d p i ∧ IsSchemeKernel d U ∧
        IsTorusGroup D ∧ Smooth U.group.X.hom ∧ ConnectedSpace U.group.X.left ∧
        IsNormalSubgroup U.inclusion ∧ Unipotent.IsUnipotent (Unipotent.closedSubgroupAlgebraicGroup U) ∧
        ∀ V : ClosedSubgroup G.val, Unipotent.IsUnipotent (Unipotent.closedSubgroupAlgebraicGroup V) →
          ∃ v : V.group ⟶ U.group, v ≫ U.inclusion = V.inclusion

end
end LinearAlgebraicGroups.Specs.SmoothDiagonalKernel
