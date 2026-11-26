import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointCocharacters
import Mathlib.AlgebraicGeometry.Morphisms.Finite

open AlgebraicGeometry CategoryTheory
open scoped Matrix

universe u

namespace LinearAlgebraicGroups.Specs.AdjointLieAutomorphisms

open AdjointRepresentation (GroupPoints TangentCoordinates conjugate)
open AdjointCocharacters (IsAdjointQuotient)
open GeometricRadicals (IsSemisimple)

noncomputable section

/-- The bracket in scalar-extended coordinates, with input indices first. -/
def coordinateBracket {k R ι : Type u} [CommRing k] [CommRing R] [Fintype ι]
    (c : ι → ι → ι → k) (f : k →+* R) (x y : ι → R) (l : ι) : R :=
  ∑ i, ∑ j, x i * y j * f (c i j l)

/-- An invertible matrix acts by a Lie automorphism on the bracket tensor. -/
def PreservesBracket {k R ι : Type u} [CommRing k] [CommRing R] [Fintype ι] [DecidableEq ι]
    (c : ι → ι → ι → k) (f : k →+* R) (M : Matrix.GeneralLinearGroup ι R) : Prop :=
  ∀ x y : ι → R, coordinateBracket c f (M.val *ᵥ x) (M.val *ᵥ y) =
    M.val *ᵥ coordinateBracket c f x y

/-- The full bracket-automorphism scheme is the closed subscheme of the
general linear group representing the bracket equations on all test rings. -/
def RepresentsBracketAutomorphisms {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    (c : ι → ι → ι → k) {A L : AffineAlgebraicGroup k} (j : A.val ⟶ L.val)
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι) : Prop :=
  IsClosedImmersion j.hom.hom.left ∧
    ∀ (R : TestAlgebra k) (M : Matrix.GeneralLinearGroup ι R),
      PreservesBracket c (algebraMap k R) M ↔
        ∃ a : GroupPoints A.val R, (l.hom.app R).hom
          (((groupPointsFunctor k).map j).app R a) = M

/-- After base change, the subgroup identifies with the open subscheme on
the connected component of the identity of the bracket-automorphism scheme. -/
def IsGeometricIdentityComponent {k : Type u} [Field k] {Q A : AffineAlgebraicGroup k}
    (i : Q.val ⟶ A.val) : Prop :=
  let K := AlgebraicClosure k
  let Abar := (groupBaseChange k K).obj A.val
  let ibar := ((groupBaseChange k K).map i).hom.hom.left
  IsOpenImmersion ibar ∧ Set.range ibar = connectedComponent (groupIdentityPoint Abar)

/-- The adjoint quotient of a characteristic-zero semisimple affine group,
in coordinates on its actual identity Lie algebra. -/
def AdjointRealization : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k), IsSemisimple G →
    ∃ (Z : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsAdjointQuotient Z q ∧ IsFinite Z.group.X.hom ∧ IsFinite q.hom.hom.left ∧
      IsSemisimple Q ∧
      ∃ s : IdentityLieStructure G.val,
        letI := s.lieRing
        letI := s.lieAlgebra
        ∃ (n : ℕ) (b : Module.Basis (ULift.{u} (Fin n)) k (Lie k G.val))
          (T : TangentCoordinates G.val (ULift.{u} (Fin n)) b)
          (L : AffineAlgebraicGroup k)
          (l : (groupPointsFunctor k).obj L.val ≅
            StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
          (A : AffineAlgebraicGroup k) (j : A.val ⟶ L.val) (i : Q.val ⟶ A.val),
          let c := fun a d r => b.repr ⁅b a, b d⁆ r
          let ρ (R : TestAlgebra k) (a : GroupPoints Q.val R) :
              Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R :=
            (l.hom.app R).hom (((groupPointsFunctor k).map (i ≫ j)).app R a)
          RepresentsBracketAutomorphisms c j l ∧
          IsClosedImmersion (i ≫ j).hom.hom.left ∧ IsGeometricIdentityComponent i ∧
          (∀ (R : TestAlgebra k) (g : GroupPoints G.val R) (v : ULift.{u} (Fin n) → R),
            let M := ρ R (((groupPointsFunctor k).map q).app R g)
            (T.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (T.equiv R v)) ∧
          AdjointRepresentation.ScalarExtension s b T l (q ≫ i ≫ j) ∧
          (∀ (R : TestAlgebra k) (a : GroupPoints Q.val R),
            PreservesBracket c (algebraMap k R) (ρ R a) ∧ (ρ R a).val.det = 1) ∧
          ∃ (m : ℕ) (r : Fin m → Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) k),
            (∀ t, PreservesBracket c (RingHom.id k) (r t)) ∧
            ∀ M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) k,
              PreservesBracket c (RingHom.id k) M →
                ∃ (a : GroupPoints Q.val (CommAlgCat.of k k)) (t : Fin m),
                  M = ρ (CommAlgCat.of k k) a * r t

end

end LinearAlgebraicGroups.Specs.AdjointLieAutomorphisms
