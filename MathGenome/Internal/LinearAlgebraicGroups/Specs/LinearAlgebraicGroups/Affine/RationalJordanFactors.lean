import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.LinearJordanFactors
import Mathlib.RingTheory.AdjoinRoot

open CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Affine

open Module

noncomputable section

/-- Rational points of a group scheme, with multiplication induced by the group law. -/
abbrev RationalPoints {k : Type u} [Field k] (G : Specs.GroupScheme k) :=
  ((groupPointsFunctor k).obj G).obj (CommAlgCat.of k k)

/-- The action of a rational group point in a finite-dimensional rational representation,
written on the represented vector space in the given basis. -/
def rationalRepresentationAction {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] {G : AffineGroupCategory k} {L : Specs.GroupScheme k}
    (b : Basis ι k V)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k ι)
    (f : Specs.RationalRepresentations.representation G L l) (g : RationalPoints G.val) :
    End k V :=
  Matrix.toLin b b
    (l.hom.app (CommAlgCat.of k k)
      (((groupPointsFunctor k).map f).app (CommAlgCat.of k k) g) :
      Matrix.GeneralLinearGroup ι k).val

/-- The two factors multiply to the original point, commute, and give its multiplicative
Jordan decomposition in every finite-dimensional rational representation. -/
def IsRationalJordanDecomposition {k : Type u} [Field k] (G : AffineGroupCategory k)
    (g s t : RationalPoints G.val) : Prop :=
  g = s * t ∧ Commute s t ∧
    ∀ {V ι : Type u} [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
      (b : Basis ι k V) (L : Specs.GroupScheme k)
      (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k ι)
      (f : Specs.RationalRepresentations.representation G L l),
      IsMultiplicativeJordanDecomposition (rationalRepresentationAction b l f g)
        (rationalRepresentationAction b l f s) (rationalRepresentationAction b l f t)

namespace RationalJordanFactorsSpec

/-- Existence and uniqueness for affine algebraic groups over perfect fields. -/
def existenceAndUniqueness : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G : Specs.AffineAlgebraicGroup k)
    (g : RationalPoints G.val),
    ∃! p : RationalPoints G.val × RationalPoints G.val,
      IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ g p.1 p.2

/-- A homomorphism carries the rational factors to the rational factors of its image. -/
def functoriality : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G H : Specs.AffineAlgebraicGroup k)
    (f : G.val ⟶ H.val) {g s t : RationalPoints G.val},
    IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ g s t →
    let φ := ((groupPointsFunctor k).map f).app (CommAlgCat.of k k)
    IsRationalJordanDecomposition ⟨H.val, H.property.1⟩ (φ g) (φ s) (φ t)

open Polynomial in
/-- Multiplication by the adjoined p-th root of a non-p-th-power gives an invertible operator.
Over the algebraic closure its semisimple factor is scalar and does not descend. -/
def imperfectFieldExample : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p], ∀ hp : 0 < p,
    ∀ a : k, (∀ b : k, b ^ p ≠ a) →
    let P : k[X] := X ^ p - C a
    let E := AdjoinRoot P
    letI : FiniteDimensional k E := (monic_X_pow_sub_C a (Nat.ne_of_gt hp)).finite_adjoinRoot
    let K := AlgebraicClosure k
    let F : End k E := Algebra.lmul k E (AdjoinRoot.root P)
    Irreducible P ∧ IsField E ∧ AdjoinRoot.root P ^ p = algebraMap k E a ∧
    IsUnit F ∧ F.charpoly = P ∧
    ∃ c : K, c ^ p = algebraMap k K a ∧
      (∃ U : End K (K ⊗[k] E),
        IsMultiplicativeJordanDecomposition (F.baseChange K) (c • 1) U) ∧
      ¬ ∃ S : End k E, S.baseChange K = c • 1

end RationalJordanFactorsSpec
end
end LinearAlgebraicGroups.Affine
