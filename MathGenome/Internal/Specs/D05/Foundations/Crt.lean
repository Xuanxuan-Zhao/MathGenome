import MathGenome.Internal.Specs.D05.Foundations.Factorization
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Independent statements for the Chinese remainder construction in
paper.tex:370–382. Quotients are allowed to be zero algebras. In particular,
neither an individual quotient nor the quotient by the product has a
`Nontrivial` hypothesis. All polynomials are formal `Polynomial K` objects. -/

noncomputable section

namespace D05.Foundations

abbrev polynomialIdeal {K : Type*} [Field K] (p : Polynomial K) :
    Ideal (Polynomial K) := Ideal.span {p}

abbrev PolynomialResidue {K : Type*} [Field K] (p : Polynomial K) :=
  Polynomial K ⧸ polynomialIdeal p

/-- The product of the finite family, with empty product one. -/
def crtProduct {K ι : Type*} [Field K] [Fintype ι]
    (q : ι → Polynomial K) : Polynomial K := ∏ i, q i

/-- The product with the indicated factor omitted. Its agreement with
`crtProduct q / q i` is a theorem, not an assumed certificate. -/
def crtCofactor {K ι : Type*} [Field K] [Fintype ι]
    (q : ι → Polynomial K) (i : ι) : Polynomial K := by
  classical
  exact ∏ j ∈ Finset.univ.erase i, q j

/-- The unital K-algebra map taking every polynomial to all its residues. -/
def polynomialResidues {K ι : Type*} [Field K] (q : ι → Polynomial K) :
    Polynomial K →ₐ[K] (∀ i, PolynomialResidue (q i)) :=
  AlgHom.pi fun i => Ideal.Quotient.mkₐ K (polynomialIdeal (q i))

end D05.Foundations

namespace D05.Specs.Crt

open D05.Foundations

local instance {α : Type*} : DecidableEq α := Classical.decEq α

def cofactorIdentity : Prop :=
  ∀ (K ι : Type*) [Field K] [Fintype ι] (q : ι → Polynomial K),
    (∀ i, (q i).Monic) → ∀ i,
      q i * crtCofactor q i = crtProduct q ∧
      crtCofactor q i = crtProduct q / q i

/-- Actual Bézout coefficients produce the polynomial representatives of
the coordinate idempotents. This permits q_i = 1. -/
def bezoutResidues : Prop :=
  ∀ (K ι : Type*) [Field K] [Fintype ι] (q : ι → Polynomial K),
    (∀ i, (q i).Monic) → (Pairwise fun i j => IsCoprime (q i) (q j)) →
    ∃ u v : ι → Polynomial K, ∀ i,
      u i * crtCofactor q i + v i * q i = 1 ∧
      ∀ j, Ideal.Quotient.mk (polynomialIdeal (q j)) (u i * crtCofactor q i) =
        if j = i then 1 else 0

/-- These representatives are idempotent and orthogonal modulo Q, and
sum to the unit modulo Q; they need not be idempotent as polynomials. -/
def residueIdempotents : Prop :=
  ∀ (K ι : Type*) [Field K] [Fintype ι] (q e : ι → Polynomial K),
    (∀ i, (q i).Monic) → (Pairwise fun i j => IsCoprime (q i) (q j)) →
    (∀ i j, Ideal.Quotient.mk (polynomialIdeal (q j)) (e i) =
      if j = i then 1 else 0) →
    (∀ i, Ideal.Quotient.mk (polynomialIdeal (crtProduct q)) (e i * e i) =
      Ideal.Quotient.mk (polynomialIdeal (crtProduct q)) (e i)) ∧
    (∀ i j, i ≠ j →
      Ideal.Quotient.mk (polynomialIdeal (crtProduct q)) (e i * e j) = 0) ∧
    Ideal.Quotient.mk (polynomialIdeal (crtProduct q)) (∑ i, e i) = 1

/-- The manuscript's explicit finite sum realizes any polynomial residues. -/
def residueInterpolation : Prop :=
  ∀ (K ι : Type*) [Field K] [Fintype ι] (q e f : ι → Polynomial K),
    (∀ i j, Ideal.Quotient.mk (polynomialIdeal (q j)) (e i) =
      if j = i then 1 else 0) →
    polynomialResidues q (∑ i, f i * e i) =
      fun j => Ideal.Quotient.mk (polynomialIdeal (q j)) (f j)

def surjectiveResidues : Prop :=
  ∀ (K ι : Type*) [Field K] [Fintype ι] (q : ι → Polynomial K),
    (∀ i, (q i).Monic) → (Pairwise fun i j => IsCoprime (q i) (q j)) →
    Function.Surjective (polynomialResidues q)

/-- Vanishing in every component is exactly divisibility by the full product;
the equality identifies the kernel as an ideal, rather than just a set. -/
def kernelResidues : Prop :=
  ∀ (K ι : Type*) [Field K] [Fintype ι] (q : ι → Polynomial K),
    (∀ i, (q i).Monic) → (Pairwise fun i j => IsCoprime (q i) (q j)) →
    RingHom.ker (polynomialResidues q).toRingHom = polynomialIdeal (crtProduct q) ∧
    ∀ f : Polynomial K, crtProduct q ∣ f ↔ ∀ i, q i ∣ f

/-- A K-algebra isomorphism with the stated value on every representative.
This formula fixes the map, rather than merely asserting abstract isomorphism. -/
def chineseRemainder : Prop :=
  ∀ (K ι : Type*) [Field K] [Fintype ι] (q : ι → Polynomial K),
    (∀ i, (q i).Monic) → (Pairwise fun i j => IsCoprime (q i) (q j)) →
    ∃ E : PolynomialResidue (crtProduct q) ≃ₐ[K] (∀ i, PolynomialResidue (q i)),
      ∀ (f : Polynomial K) (i : ι),
        E (Ideal.Quotient.mk (polynomialIdeal (crtProduct q)) f) i =
          Ideal.Quotient.mk (polynomialIdeal (q i)) f

/-- The degenerate cases are zero algebras, not excluded instances. -/
def emptyFamily : Prop :=
  ∀ (K ι : Type*) [Field K] [Fintype ι] [IsEmpty ι] (q : ι → Polynomial K),
    crtProduct q = 1 ∧ Subsingleton (PolynomialResidue (crtProduct q)) ∧
      Subsingleton (∀ i, PolynomialResidue (q i))

def unitResidue : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K),
    IsUnit p → Subsingleton (PolynomialResidue p)

end D05.Specs.Crt
