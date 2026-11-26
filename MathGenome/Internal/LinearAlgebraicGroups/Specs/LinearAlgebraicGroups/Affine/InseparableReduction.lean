import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Perfect

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.InseparableReduction
noncomputable section

abbrev PlaneIndex := ULift.{u} (Fin 2)

abbrev Plane (k : Type u) [CommRing k] := MvPolynomial PlaneIndex.{u} k

abbrev x (k : Type u) [CommRing k] : Plane k := MvPolynomial.X (ULift.up 1)
abbrev y (k : Type u) [CommRing k] : Plane k := MvPolynomial.X (ULift.up 0)

def relation {k : Type u} [CommRing k] (p : ℕ) (c : k) : Plane k :=
  y k ^ p - MvPolynomial.C c * x k ^ p

abbrev relationIdeal {k : Type u} [CommRing k] (p : ℕ) (c : k) : Ideal (Plane k) :=
  Ideal.span {relation p c}

abbrev Coordinates {k : Type u} [CommRing k] (p : ℕ) (c : k) :=
  Plane k ⧸ relationIdeal p c

/-- The equation is integral over the ground field when the coefficient is not a p-th power. -/
def IntegralCoordinates : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (c : k), (∀ b : k, b ^ p ≠ c) → IsDomain (Coordinates p c)

/-- The base change is the indicated quotient, with the coordinate classes preserved.
Over every field containing a root, the relation is the p-th power of the indicated line,
whose class in that base change is nonzero. -/
def ScalarExtension : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP k p] (c : k),
    ∃ e : K ⊗[k] Coordinates p c ≃ₐ[K] Coordinates p (algebraMap k K c),
      (∀ f : Plane k, e (1 ⊗ₜ[k] Ideal.Quotient.mk (relationIdeal p c) f) =
        Ideal.Quotient.mk (relationIdeal p (algebraMap k K c)) (MvPolynomial.map (algebraMap k K) f)) ∧
      ∀ a : K, a ^ p = algebraMap k K c →
        let line := y K - MvPolynomial.C a * x K
        let z := Ideal.Quotient.mk (relationIdeal p (algebraMap k K c)) line
        relation p (algebraMap k K c) = line ^ p ∧ z ≠ 0 ∧ z ^ p = 0

/-- The additive plane uses the Hopf law with primitive coordinate variables. Its quotient
by the relation defines a closed subgroup with reduced, geometrically nonreduced and
nonsmooth underlying scheme over the ground field. -/
def ClosedSubgroupExample : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (c : k), (∀ b : k, b ^ p ≠ c) →
    ∃ h : StandardGroups.HopfOperations k (Plane k),
      letI := h.hopf
      let A := CommHopfAlgCat.of k (Plane k)
      (∀ i : PlaneIndex.{u}, h.delta (MvPolynomial.X i) =
        (MvPolynomial.X i : Plane k) ⊗ₜ[k] (1 : Plane k) +
          (1 : Plane k) ⊗ₜ[k] (MvPolynomial.X i : Plane k)) ∧
      (∀ i : PlaneIndex.{u}, h.epsilon (MvPolynomial.X i) = 0) ∧
      (∀ i : PlaneIndex.{u}, h.inverse (MvPolynomial.X i) = -MvPolynomial.X i) ∧
      h.delta (relation p c) = relation p c ⊗ₜ[k] (1 : Plane k) +
        (1 : Plane k) ⊗ₜ[k] relation p c ∧
      ∃ _ : (relationIdeal p c).IsHopfIdeal k,
        let G := specGroup (hopfQuotient A (relationIdeal p c))
        let i := specGroupMap (hopfQuotientMap A (relationIdeal p c))
        IsClosedImmersion i.hom.hom.left ∧ IsAffine G.X.left ∧
          LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom ∧ IsReduced G.X.left ∧
          ¬ GeometricallyReduced G.X.hom ∧ ¬ Smooth G.X.hom

/-- Over every nonperfect field there is a reduced affine algebraic group whose
structure morphism is neither geometrically reduced nor smooth. -/
def NonperfectFieldExample : Prop :=
  ∀ (k : Type u) [Field k], ¬ PerfectField k →
    ∃ G : AffineAlgebraicGroup k, IsReduced G.val.X.left ∧
      ¬ GeometricallyReduced G.val.X.hom ∧ ¬ Smooth G.val.X.hom

end

end LinearAlgebraicGroups.Specs.InseparableReduction
