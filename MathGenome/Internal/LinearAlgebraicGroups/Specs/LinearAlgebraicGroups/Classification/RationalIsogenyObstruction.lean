import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.TypeAOneLattices
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.TorsorObstruction
import Mathlib.Basic.Real.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace LinearAlgebraicGroups.Specs.RationalIsogenyObstruction

open Fppf TorsorObstruction TypeAOneLattices
open GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open CentralIsogenies (IsCentralIsogeny)
open SmoothnessAndIsogenies (rootsOfUnityCoordinates)
open DiagonalizableGroups (rootsOfUnityPoints)
open GeneralLinearCentralIsogeny (pointMap)
open StandardGroups (multiplicativePoints)
open Unipotent (Index)

noncomputable section

variable {k : Type u} [Field k] {n : ℕ}
variable {G S M : AffineAlgebraicGroup k}
variable {g : MatrixPoints G n} {s : SpecialMatrixPoints S n}
variable {a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k}

abbrev rationalAlgebra (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

/-- The two presentations of the spectrum of the base field over itself. -/
def rationalTestIso (k : Type u) [Field k] :
    (testSpec k).obj (op (rationalAlgebra k)) ≅ fieldBase k :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom (algebraMap k k))
    rw [Algebra.algebraMap_self]
    simp)

/-- The image of a matrix in the rational points of the actual scalar quotient. -/
def projectMatrix (Q : ScalarQuotient g s a)
    (A : Matrix.GeneralLinearGroup (Index.{u} n) k) : fieldBase k ⟶ Q.P.val.X :=
  (rationalTestIso k).inv ≫ g.inv.app (rationalAlgebra k) A ≫ Q.q.hom.hom

/-- The rational image of the determinant-one group in the scheme quotient. -/
def HasSpecialLift (Q : ScalarQuotient g s a) (x : fieldBase k ⟶ Q.P.val.X) : Prop :=
  ∃ b : fieldBase k ⟶ S.val.X, b ≫ Q.map.hom.hom = x

/-- The class of the actual scheme fibre, with right translation by the
specified subgroup. The section formula expresses the scheme pullback on
every test scheme over the field. -/
def IsSchemeFibreClass (Q : ScalarQuotient g s a) (N : ClosedSubgroup S.val)
    (x : fieldBase k ⟶ Q.P.val.X) (c : H1fppf k N.group) : Prop :=
  ∃ y : RationalPoints N, IsFibreClass N y c ∧
    ∀ (U : Over (fieldBase k)) (b : U.left ⟶ S.val.X),
      projectSection N b =
        (rightQuotientSheaf N).obj.map (Over.mkIdTerminal.from U).left.op y ↔
      b ≫ Q.map.hom.hom = U.hom ≫ x

/-- Rational points of the scalar quotient have matrix representatives, and
the obstruction to a determinant-one representative is the class of the
scheme fibre under the scalar roots of unity. -/
def RationalLifting : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    ∀ (G S M : AffineAlgebraicGroup k) (g : MatrixPoints G n) (s : SpecialMatrixPoints S n)
      (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k),
      ∃ Q : ScalarQuotient g s a, IsCentralIsogeny Q.map ∧
        ∃ (N : ClosedSubgroup S.val) (e : N.group ≅ specGroup (rootsOfUnityCoordinates k n))
          (r : (groupPointsFunctor k).obj (specGroup (rootsOfUnityCoordinates k n)) ≅
            rootsOfUnityPoints k n),
          IsSchemeKernel Q.map N ∧
          (∀ (R : TestAlgebra k) (z : Points N.group.X R),
            Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap N.inclusion R z)) =
              Matrix.GeneralLinearGroup.scalar (Index.{u} n)
                (((groupPointsFunctor k).mapIso e ≪≫ r).hom.app R z).val) ∧
          Function.Surjective (projectMatrix Q) ∧
          (∀ A, HasSpecialLift Q (projectMatrix Q A) ↔
            ∃ t : kˣ, t ^ n = Matrix.GeneralLinearGroup.det A) ∧
          ∃ δ : (fieldBase k ⟶ Q.P.val.X) → H1fppf k N.group,
            (∀ x, IsSchemeFibreClass Q N x (δ x)) ∧
            ∀ x, HasSpecialLift Q x ↔ δ x = fieldNeutralClass N.group

/-- Every negative-determinant representative over the reals obstructs a
special-linear lift in rank two. -/
def NegativeDeterminantObstructs : Prop :=
  ∀ (G S M : AffineAlgebraicGroup ℝ) (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
    (a : (groupPointsFunctor ℝ).obj M.val ≅ multiplicativePoints ℝ)
    (Q : ScalarQuotient g s a) (A : Matrix.GeneralLinearGroup (Index.{0} 2) ℝ),
    (Matrix.GeneralLinearGroup.det A : ℝ) < 0 → ¬ HasSpecialLift Q (projectMatrix Q A)

/-- The real projective class of the reflection diag(−1, 1) does not lift. -/
def RealCounterexample : Prop :=
  ∃ (G S M : AffineAlgebraicGroup ℝ) (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
    (a : (groupPointsFunctor ℝ).obj M.val ≅ multiplicativePoints ℝ)
    (Q : ScalarQuotient g s a) (A : Matrix.GeneralLinearGroup (Index.{0} 2) ℝ),
    IsCentralIsogeny Q.map ∧
    A.val = Matrix.diagonal (fun i : Index.{0} 2 ↦ if i = ⟨0⟩ then -1 else 1) ∧
    (Matrix.GeneralLinearGroup.det A : ℝ) < 0 ∧
    ¬ HasSpecialLift Q (projectMatrix Q A)

end
end LinearAlgebraicGroups.Specs.RationalIsogenyObstruction
