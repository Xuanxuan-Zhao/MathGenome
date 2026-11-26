import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.PrimitiveLine
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open CategoryTheory MvPolynomial
open scoped BigOperators

universe u

noncomputable section

namespace LinearAlgebraicGroups.Specs.GeometricReductivity

open AdjointRepresentation (GroupPoints)
open GeometricRadicals (IsSemisimple)
open RootWeightAction (Representation act extendVector)

variable {k I J : Type u} [Field k] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- The vector in the given basis, viewed in degree one of its symmetric algebra. -/
def linearPolynomial {R : Type u} [CommRing R] (v : J → R) : MvPolynomial J R :=
  ∑ j, v j • X j

/-- The action on the symmetric algebra induced by the action on the basis vectors. -/
def polynomialAction {R : Type u} [CommRing R] (M : Matrix J J R) :
    MvPolynomial J R →ₐ[R] MvPolynomial J R :=
  bind₁ (fun j ↦ linearPolynomial (fun i ↦ M i j))

/-- Scheme invariance of a symmetric tensor, tested after scalar extension to
every commutative test algebra. -/
def SymmetricFixed {H : AffineAlgebraicGroup k} (ρ : Representation H.val J)
    (f : MvPolynomial J k) : Prop :=
  ∀ (R : TestAlgebra k) (g : GroupPoints H.val R),
    polynomialAction (ρ.app R g).val (f.map (algebraMap k R)) = f.map (algebraMap k R)

/-- The quotient onto the trivial line. Equivariance is tested over all
commutative test algebras by extending its row of coefficients. -/
def IsTrivialQuotient {H : AffineAlgebraicGroup k} (ρ : Representation H.val J)
    (q : (J → k) →ₗ[k] k) : Prop :=
  Function.Surjective q ∧
  ∀ (R : TestAlgebra k) (g : GroupPoints H.val R) (x : J → R),
    ∑ j, algebraMap k R (q (Pi.single j 1)) * (act ρ R g x) j =
      ∑ j, algebraMap k R (q (Pi.single j 1)) * x j

/-- The degree-d component of the symmetric algebra in the chosen basis is
the space of homogeneous polynomials of degree d. Evaluation at the row
of the quotient gives the scalar coefficient in degree d on the trivial line. -/
def InvariantLifting : Prop :=
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : AffineAlgebraicGroup k), IsSemisimple H →
    ∀ {J : Type u} [Fintype J] [DecidableEq J] (ρ : Representation H.val J)
      (q : (J → k) →ₗ[k] k), IsTrivialQuotient ρ q →
      ∃ (d : ℕ) (f : MvPolynomial J k), 0 < d ∧ f.IsHomogeneous d ∧
        SymmetricFixed ρ f ∧ MvPolynomial.eval (fun j ↦ q (Pi.single j 1)) f = 1

/-- In matrix coordinates this is a lift of evaluation at the identity from
the dual of the endomorphism representation. Coordinate function (i,j)
is sent to F i j. Its action is by substitution of the inverse conjugation. -/
def IsEndomorphismLift {H : AffineAlgebraicGroup k}
    (ρ : Representation H.val J) (S : Representation H.val I)
    (q : (J → k) →ₗ[k] k) (F : Matrix I I (J → k)) : Prop :=
  (∀ i j, q (F i j) = (1 : Matrix I I k) i j) ∧
  ∀ (R : TestAlgebra k) (g : GroupPoints H.val R) (l : J),
    Matrix.of (fun i j ↦ act ρ R g (extendVector R (F i j)) l) =
      ((S.app R g)⁻¹).val * Matrix.of (fun i j ↦ algebraMap k R (F i j l)) * (S.app R g).val

end LinearAlgebraicGroups.Specs.GeometricReductivity
