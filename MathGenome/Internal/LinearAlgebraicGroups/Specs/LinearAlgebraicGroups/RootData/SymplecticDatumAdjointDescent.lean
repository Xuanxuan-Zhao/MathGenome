import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.MatrixAlgebra

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.SymplecticDatumAdjointDescent

open SymplecticMatrixStructure (Indices PointGroup symplecticPoints mapSymplecticPoint)

noncomputable section

abbrev MatrixAlgebra (I R : Type*) := Matrix (Indices I) (Indices I) R

variable {I R : Type u} [Fintype I] [DecidableEq I] [CommRing R]

/-- The symplectic adjoint. The inverse of the hyperbolic matrix `J` is `-J`. -/
def adjoint (X : MatrixAlgebra I R) : MatrixAlgebra I R :=
  (-Matrix.J I R) * X.transpose * Matrix.J I R

def IsScalarMuTwo (X : MatrixAlgebra I R) : Prop :=
  ∃ a : R, a * a = 1 ∧ X = Matrix.scalar (Indices I) a

def conjugateMatrix (g : PointGroup I R) (X : MatrixAlgebra I R) : MatrixAlgebra I R :=
  g.val * X * (g⁻¹).val

/-- The represented symplectic group is the isometry group of the split matrix involution. -/
def AdjointIdentities : Prop :=
  ∀ (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R],
    (∀ X : MatrixAlgebra I R, adjoint (adjoint X) = X) ∧
    (∀ X Y : MatrixAlgebra I R, adjoint (X * Y) = adjoint Y * adjoint X) ∧
    (∀ a : R, adjoint (Matrix.scalar (Indices I) a) = Matrix.scalar (Indices I) a) ∧
    (∀ X : MatrixAlgebra I R, X ∈ Matrix.symplecticGroup I R ↔ adjoint X * X = 1) ∧
    (∀ {S : Type u} [CommRing S] (f : R →+* S) (X : MatrixAlgebra I R),
      (adjoint X).map f = adjoint (X.map f))

/-- Matrix coordinates model extension of scalars of the algebra with involution.
The formula uses the copy of the test algebra on the left of the tensor product. -/
def MatrixScalarExtension : Prop :=
  ∀ (k I R : Type u) [Field k] [Fintype I] [DecidableEq I] [CommRing R] [Algebra k R],
    ∃ e : R ⊗[k] MatrixAlgebra I k ≃ₐ[R] MatrixAlgebra I R,
      (∀ (r : R) (X : MatrixAlgebra I k), e (r ⊗ₜ[k] X) = r • X.map (algebraMap k R)) ∧
      (∀ (r : R) (X : MatrixAlgebra I k), e (r ⊗ₜ[k] adjoint X) = adjoint (e (r ⊗ₜ[k] X)))

variable {k : Type u} [Field k]

abbrev GroupPoints (G : GroupScheme k) (R : TestAlgebra k) :=
  ((groupPointsFunctor k).obj G).obj R

/-- The all-algebras description of the scheme centre used to form the quotient. -/
def ScalarCentre {G : GroupScheme k}
    (c : (groupPointsFunctor k).obj G ≅ symplecticPoints k I)
    (Z : ClosedSubgroup G) : Prop :=
  ∀ (R : TestAlgebra k) (g : Points G.X R),
    (∃ z : Points Z.group.X R, z ≫ Z.inclusion.hom.hom = g) ↔
      IsScalarMuTwo (show PointGroup I R from c.hom.app R g).val

/-- The fppf quotient by the scalar scheme centre acts on the matrix algebra
and preserves its involution. On the represented isometry group, the action
is inner after any fppf lift to the symplectic group. -/
def AdjointQuotientAction : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [Nonempty I]
    (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I)
    (Z : ClosedSubgroup G.val), ScalarCentre c Z →
    ∃ (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsSchemeKernel q Z ∧
      SchemeDerivedGroup.RepresentsQuotient Z q ∧
      (∀ (R : TestAlgebra k) (a : GroupPoints Q.val R),
        ∃ (S : TestAlgebra k) (f : R ⟶ S) (g : GroupPoints G.val S),
          f.hom.toRingHom.FaithfullyFlat ∧ f.hom.toRingHom.FinitePresentation ∧
          ((groupPointsFunctor k).map q).app S g =
            ((groupPointsFunctor k).obj Q.val).map f a) ∧
      ∃ (action : ∀ R : TestAlgebra k, GroupPoints Q.val R →*
            (MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R))
        (isometryAction : ∀ R : TestAlgebra k, GroupPoints Q.val R →* MulAut (PointGroup I R)),
        (∀ R, Function.Injective (action R)) ∧
        (∀ (R : TestAlgebra k) (a : GroupPoints Q.val R) X,
          action R a (adjoint X) = adjoint (action R a X)) ∧
        (∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : GroupPoints Q.val R) X,
          (action R a X).map f.hom = action S
            (((groupPointsFunctor k).obj Q.val).map f a) (X.map f.hom)) ∧
        (∀ (R : TestAlgebra k) (g : GroupPoints G.val R) X,
          action R (((groupPointsFunctor k).map q).app R g) X =
            conjugateMatrix (c.hom.app R g) X) ∧
        (∀ (R : TestAlgebra k) (a : GroupPoints Q.val R) (h : PointGroup I R),
          (isometryAction R a h).val = action R a h.val) ∧
        (∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : GroupPoints Q.val R) (h : PointGroup I R),
          mapSymplecticPoint f.hom.toRingHom (isometryAction R a h) =
            isometryAction S (((groupPointsFunctor k).obj Q.val).map f a)
              (mapSymplecticPoint f.hom.toRingHom h)) ∧
        ∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : GroupPoints Q.val R)
          (g : GroupPoints G.val S) (h : PointGroup I R),
          ((groupPointsFunctor k).map q).app S g =
            ((groupPointsFunctor k).obj Q.val).map f a →
          mapSymplecticPoint f.hom.toRingHom (isometryAction R a h) =
            (show PointGroup I S from c.hom.app S g) * mapSymplecticPoint f.hom.toRingHom h *
              (show PointGroup I S from c.hom.app S g)⁻¹

end

end LinearAlgebraicGroups.Specs.SymplecticDatumAdjointDescent
