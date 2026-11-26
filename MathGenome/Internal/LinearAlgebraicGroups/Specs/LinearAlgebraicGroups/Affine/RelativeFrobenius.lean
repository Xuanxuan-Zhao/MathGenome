import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Derivation.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Coalgebra
open scoped TensorProduct DualNumber

universe u

namespace LinearAlgebraicGroups.Specs.RelativeFrobenius

noncomputable section

/-- Extend the scalars of the whole Hopf algebra on the left. -/
def extendAlong {k K : Type u} [Field k] [Field K]
    (σ : k →+* K) (A : HopfAlgebraCategory k) : HopfAlgebraCategory K :=
  letI := σ.toAlgebra
  extendedHopf K A

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The left tensor factor is the new field, with its old-field action
given by Frobenius. -/
abbrev twistCoordinates (A : HopfAlgebraCategory k) : HopfAlgebraCategory k :=
  extendAlong (frobenius k p) A

abbrev twist (A : HopfAlgebraCategory k) : GroupScheme k :=
  specGroup (twistCoordinates k p A)

def TwistType := ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
  HopfAlgebraCategory k → GroupScheme k

def TwistIsBaseChange : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k),
    letI := (frobenius k p).toAlgebra
    Nonempty (twist k p A ≅ (groupBaseChange k k).obj (specGroup A))

/-- Pure tensor in the scalar extension, with the new scalar listed first. -/
def scalarTensor {k K : Type u} [Field k] [Field K]
    (σ : k →+* K) (A : HopfAlgebraCategory k) (c : K) (a : A) : extendAlong σ A :=
  letI := σ.toAlgebra
  c ⊗ₜ[k] a

def PullbackFormula (A : HopfAlgebraCategory k) (f : twistCoordinates k p A ⟶ A) : Prop :=
  ∀ (c : k) (a : A), f.hom (scalarTensor (frobenius k p) A c a) = c • a ^ p

def RelativeFrobeniusExists : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (A : HopfAlgebraCategory k),
    ∃! f : twistCoordinates k p A ⟶ A, PullbackFormula k p A f

def RelativeFrobeniusMorphism : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (A : HopfAlgebraCategory k),
    ∃! F : specGroup A ⟶ twist k p A,
      ∃ f : twistCoordinates k p A ⟶ A,
        PullbackFormula k p A f ∧ F = specGroupMap f

/-- The quotient for the additive kernel (also used as a ring model for the
multiplicative kernel after translation of its coordinate). -/
abbrev alphaIdeal : Ideal (Polynomial k) :=
  Ideal.span {(Polynomial.X : Polynomial k) ^ p}

abbrev muIdeal : Ideal (LaurentPolynomial k) :=
  Ideal.span {(LaurentPolynomial.T 1 : LaurentPolynomial k) ^ p - 1}

abbrev AlphaCoordinates := Polynomial k ⧸ alphaIdeal k p
abbrev MuCoordinates := LaurentPolynomial k ⧸ muIdeal k p

def KernelCoordinateIdeals : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    ∀ (A M : HopfAlgebraCategory k)
      (eA : A ≃ₐ[k] Polynomial k) (eM : M ≃ₐ[k] LaurentPolynomial k),
      (Bialgebra.counitAlgHom k A) (eA.symm Polynomial.X) = 0 →
      (Bialgebra.counitAlgHom k M) (eM.symm (LaurentPolynomial.T 1)) = 1 →
      ∀ (f : twistCoordinates k p A ⟶ A) (g : twistCoordinates k p M ⟶ M),
        PullbackFormula k p A f → PullbackFormula k p M g →
        (kernelIdeal f).map eA.toAlgHom = alphaIdeal k p ∧
        (kernelIdeal g).map eM.toAlgHom = muIdeal k p

def alphaCoordinate : AlphaCoordinates k p :=
  Ideal.Quotient.mk (alphaIdeal k p) Polynomial.X

def muCoordinate : MuCoordinates k p :=
  Ideal.Quotient.mk (muIdeal k p) (LaurentPolynomial.T 1)

/-- The Hopf quotient gives the scheme kernel and its closed embedding, with
the prescribed presentation of the coordinate ring over the ambient ring. -/
def PresentsSchemeKernel {A B : HopfAlgebraCategory k} (f : B ⟶ A)
    {C : Type u} [CommRing C] [Algebra k C] (e : A ≃ₐ[k] C) (I : Ideal C) : Prop :=
  ∃ h : (kernelIdeal f).IsHopfIdeal k,
    letI := h
    let Q := hopfQuotient A (kernelIdeal f)
    let i := specGroupMap (hopfQuotientMap A (kernelIdeal f))
    IsPullback i (specGroupMap (hopfUnit Q)) (specGroupMap f) (specGroupMap (hopfCounit B)) ∧
    IsClosedImmersion i.hom.hom.left ∧
    ∃ j : (A ⧸ kernelIdeal f) ≃ₐ[k] (C ⧸ I),
      j.toAlgHom.comp (Ideal.Quotient.mkₐ k (kernelIdeal f)) =
        (Ideal.Quotient.mkₐ k I).comp e.toAlgHom

def FrobeniusKernelSchemes : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    ∀ (A M : HopfAlgebraCategory k)
      (eA : A ≃ₐ[k] Polynomial k) (eM : M ≃ₐ[k] LaurentPolynomial k),
      (Bialgebra.counitAlgHom k A) (eA.symm Polynomial.X) = 0 →
      (Bialgebra.counitAlgHom k M) (eM.symm (LaurentPolynomial.T 1)) = 1 →
      ∀ (f : twistCoordinates k p A ⟶ A) (g : twistCoordinates k p M ⟶ M),
        PullbackFormula k p A f → PullbackFormula k p M g →
        PresentsSchemeKernel k f eA (alphaIdeal k p) ∧
        PresentsSchemeKernel k g eM (muIdeal k p)

def KernelLengths : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    Nonempty (Module.Basis (Fin p) k (AlphaCoordinates k p)) ∧
    Nonempty (Module.Basis (Fin p) k (MuCoordinates k p))

/-- A point over an extension is a map of `k`-algebras to the extension field,
equivalently a rational point of the base-changed scheme. -/
def KernelFieldPoints : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : Type u) [Field K] [Algebra k K],
    (∃! _f : AlphaCoordinates k p →ₐ[k] K, True) ∧
    (∃! _g : MuCoordinates k p →ₐ[k] K, True)

/-- The tangent space at the point with coordinate `b` is given by identity
lifts to dual numbers. Its linear coordinate is the coefficient of `ε`. -/
def HasTangentCoordinate {C : Type u} [CommRing C] [Algebra k C] (x : C) (b : k) : Prop :=
  ∃ q : C →ₐ[k] k, q x = b ∧
    letI : Algebra C k := q.toRingHom.toAlgebra
    ∃ L : Derivation k C k ≃ₗ[k] k,
      (∀ D, L D = D x) ∧
      ∃ e : { f : C →ₐ[k] k[ε] // (TrivSqZeroExt.fstHom k k k).comp f = q } ≃
          Derivation k C k,
        (∀ f (y : C), e f y = (f.val y).snd) ∧
        ∀ a : k, (e.symm (L.symm a)).val x = algebraMap k k[ε] b + a • ε

def KernelTangentSpaces : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    HasTangentCoordinate k (alphaCoordinate k p) 0 ∧
    HasTangentCoordinate k (muCoordinate k p) 1

end
end LinearAlgebraicGroups.Specs.RelativeFrobenius
