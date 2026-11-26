import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RelativeFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Basic.Real.Basic

open AlgebraicGeometry CategoryTheory LaurentPolynomial
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.PowerMapExamples

noncomputable section

/-- Multiplication of Laurent exponents by `n`. -/
def scaleExponents (n : ℕ) : ℤ →+ ℤ where
  toFun m := (n : ℤ) * m
  map_zero' := mul_zero _
  map_add' := mul_add _

variable (k : Type u) [Field k]

abbrev torusCoordinates : HopfAlgebraCategory k :=
  CommHopfAlgCat.of k (LaurentPolynomial k)

/-- The Hopf pullback of the power morphism on the Laurent coordinate algebra. -/
def powerPullback (n : ℕ) : torusCoordinates k ⟶ torusCoordinates k :=
  CommHopfAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k (scaleExponents n))

abbrev powerMorphism (n : ℕ) : specGroup (torusCoordinates k) ⟶ specGroup (torusCoordinates k) :=
  specGroupMap (powerPullback k n)

def powerAlgebraHom (n : ℕ) : LaurentPolynomial k →ₐ[k] LaurentPolynomial k :=
  (powerPullback k n).hom.toAlgHom

def PowerMapFiniteFaithfullyFlat : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    let f := powerAlgebraHom k n
    let S := Algebra.adjoin k ({T (n : ℤ), T (-(n : ℤ))} : Set (LaurentPolynomial k))
    let g := (powerMorphism k n).hom.hom.left
    Function.Injective f ∧
    f.range = S ∧
    (∃ b : Module.Basis (Fin n) S (LaurentPolynomial k),
      ∀ i, b i = (T 1 : LaurentPolynomial k) ^ (i : ℕ)) ∧
    IsFinite g ∧ Flat g ∧ Surjective g

/-- A point of the Laurent spectrum is read as a unit by evaluating `t`. -/
def pointUnit {R : Type u} [CommRing R] [Algebra k R] (a : LaurentPolynomial k →ₐ[k] R) : Rˣ :=
  Units.map a.toMonoidHom (isUnit_T (R := k) 1).unit

def PowerMapOnPoints : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (R : Type u) [CommRing R] [Algebra k R]
    (a : LaurentPolynomial k →ₐ[k] R),
    pointUnit k (a.comp (powerAlgebraHom k n)) = pointUnit k a ^ n

def RealSquaringNotSurjective : Prop :=
  ¬ Function.Surjective (fun x : ℝˣ => x ^ (2 : ℕ))

open RelativeFrobenius in
/-- On the coordinates of the additive Frobenius kernel, the identity is evaluation at zero. -/
def alphaIdentityPullback (p : ℕ) (hp : 0 < p) : AlphaCoordinates k p →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (Polynomial.aeval (0 : k)) fun _ h =>
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (show (Polynomial.X : Polynomial k) ^ p ∈ RingHom.ker (Polynomial.aeval (0 : k)) by
        change Polynomial.aeval (0 : k) ((Polynomial.X : Polynomial k) ^ p) = 0
        rw [map_pow, Polynomial.aeval_X, zero_pow hp.ne']))) h

open RelativeFrobenius in
def AlphaIdentitySurjectiveNotFlat : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    let g := Spec.map (CommRingCat.ofHom
      (alphaIdentityPullback k p (Fact.out : p.Prime).pos).toRingHom)
    IsClosedImmersion g ∧ Surjective g ∧ ¬ Flat g

open RelativeFrobenius in
/-- The same assertion for the actual identity section in any Hopf presentation
of the additive Frobenius kernel. -/
def AlphaIdentityInHopfPresentation : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k), (A ≃ₐ[k] AlphaCoordinates k p) →
    let e := η[(specGroup A).X].left
    IsClosedImmersion e ∧ Surjective e ∧ ¬ Flat e

end

end LinearAlgebraicGroups.Specs.PowerMapExamples
