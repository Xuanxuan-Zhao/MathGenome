import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RationalCocharacter
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralSeries
import Mathlib.RingTheory.Ideal.Cotangent

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.SplitContractingRadical

open BorelProper (IsParabolic)
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsReductive)
open RankOneFlag (SameSubgroup)
open StandardParabolicLevi (IsContractingRadical)
open Unipotent (IsSplitUnipotent closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics
  (LimitDecomposition orbit polynomialAlgebra polynomialToLaurent)

/-- On the punctured line the action on the contracting subgroup agrees with
conjugation by the cocharacter, as tested on all ground-field algebras. -/
def IsConjugationExtension {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {c : Cocharacter G.val} (D : LimitDecomposition c) {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ D.contracting.group) (action : A →ₐ[k] Polynomial A) : Prop :=
  let inG (R : TestAlgebra k) (x : A →ₐ[k] R) : Points G.val.X R :=
    (testSpec k).map (CommAlgCat.ofHom x).op ≫ (e.hom ≫ D.contracting.inclusion).hom.hom
  ∀ (R : TestAlgebra k) (x : A →ₐ[k] R),
    mapPoints (polynomialToLaurent R)
        (inG (polynomialAlgebra R) ((Polynomial.mapAlgHom x).comp action)) =
      orbit c (inG R x)

/-- The contracting subgroup has polynomial coordinates of positive weights
whose classes form a basis of the cotangent space at the identity. -/
def ContractingPolynomialCoordinates : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (c : Cocharacter G.val) (D : LimitDecomposition c)
      (A : HopfAlgebraCategory k) (e : specGroup A ≅ D.contracting.group),
      let ε := Bialgebra.counitAlgHom k A
      let I := RingHom.ker ε.toRingHom
      ∃ (n : ℕ) (weight : Fin n → ℕ)
        (coordinates : MvPolynomial (Fin n) k ≃ₐ[k] A) (action : A →ₐ[k] Polynomial A),
        IsConjugationExtension D e action ∧
        (∀ i, 0 < weight i ∧
          action (coordinates (MvPolynomial.X i)) =
            Polynomial.monomial (weight i) (coordinates (MvPolynomial.X i))) ∧
        ∃ (atIdentity : ∀ i, ε (coordinates (MvPolynomial.X i)) = 0)
          (basis : Module.Basis (Fin n) k I.Cotangent),
          ∀ i, basis i = I.toCotangent ⟨coordinates (MvPolynomial.X i), atIdentity i⟩

/-- The contracting subgroup of a given cocharacter is the unipotent radical
of its limit parabolic over the ground field and after geometric base change. -/
def ContractingSubgroupIsRadical : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (c : Cocharacter G.val) (D : LimitDecomposition c), IsContractingRadical D

/-- The contracting subgroup of a ground-field cocharacter of a connected
reductive group admits a split unipotent series over the ground field. -/
def SplitContractingSubgroup : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (c : Cocharacter G.val) (D : LimitDecomposition c),
      IsSplitUnipotent (closedSubgroupAlgebraicGroup D.contracting)

/-- Every ground-field parabolic has a ground-field split unipotent radical,
realized as the contracting subgroup of a cocharacter defining the parabolic. -/
def ParabolicSplitRadical : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P →
    ∃ (c : Cocharacter G.val) (D : LimitDecomposition c),
      SameSubgroup P D.parabolic ∧ IsContractingRadical D ∧
        IsSplitUnipotent (closedSubgroupAlgebraicGroup D.contracting)

end LinearAlgebraicGroups.Specs.SplitContractingRadical
