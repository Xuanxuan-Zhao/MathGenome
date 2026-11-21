import MathGenome.Internal.Specs.D07.Ch09.ProductIntersection
import MathGenome.Internal.Specs.D07.Ch09.QuotientConstruction
import MathGenome.Internal.Specs.D07.Ch08.PrincipalDivisibility

/-!
Independent statements for K07.09.crt_finite_integer, paper.tex:1755–1780.
The chapter assumes commutative unital rings, allowing the zero ring.
Finite index types include the empty type; ideals need not be proper.
Integer coprimality is stated as gcd = 1, not as an assumed Bezout certificate.
Congruence modulo n is expressed by n dividing the difference.
-/

universe u v

namespace Specs.D07.Ch09.CrtFiniteInteger

open scoped BigOperators

/-- The finite CRT is the natural reduction map, together with the ideal identity. -/
def FiniteCRT : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] (I : ι → Ideal R),
    (∀ i j, i ≠ j → Comaximal.comaximalPredicateValue (I i) (I j)) →
      (⨅ i, I i) = ∏ i, I i ∧
      ∃ e : (R ⧸ ⨅ i, I i) ≃+* ∀ i, R ⧸ I i,
        ∀ r i, e (Ideal.Quotient.mk (⨅ i, I i) r) i = Ideal.Quotient.mk (I i) r

/-- Bezout makes the principal integer ideals pairwise comaximal; their
product and intersection are the principal ideal of the product of moduli. -/
def IntegerIdealData : Prop :=
  ∀ (ι : Type v) [Fintype ι] (n : ι → ℤ), (∀ i, 0 < n i) →
    (∀ i j, i ≠ j → Int.gcd (n i) (n j) = 1) →
      (∀ i j, i ≠ j → Comaximal.comaximalPredicateValue
        (Ideal.span {n i}) (Ideal.span {n j})) ∧
      (∏ i, Ideal.span {n i}) = Ideal.span {∏ i, n i} ∧
      (⨅ i, Ideal.span {n i}) = Ideal.span {∏ i, n i}

/-- The integer quotient isomorphism has the same coordinate reductions
as the general ring CRT. This is its integer specialization. -/
def IntegerRingCRT : Prop :=
  ∀ (ι : Type v) [Fintype ι] (n : ι → ℤ), (∀ i, 0 < n i) →
    (∀ i j, i ≠ j → Int.gcd (n i) (n j) = 1) →
      ∃ e : (ℤ ⧸ Ideal.span {∏ i, n i}) ≃+* ∀ i, ℤ ⧸ Ideal.span {n i},
        ∀ r i, e (Ideal.Quotient.mk _ r) i = Ideal.Quotient.mk _ r

/-- Every prescribed family of integer residues has a simultaneous solution. -/
def IntegerExistence : Prop :=
  ∀ (ι : Type v) [Fintype ι] (n : ι → ℤ), (∀ i, 0 < n i) →
    (∀ i j, i ≠ j → Int.gcd (n i) (n j) = 1) →
      ∀ a : ι → ℤ, ∃ x : ℤ, ∀ i, n i ∣ x - a i

/-- Two integers have all the same residues iff they agree modulo N.
In particular any two solutions are unique modulo N, and every translate
by a multiple of N remains a solution. -/
def IntegerUniqueness : Prop :=
  ∀ (ι : Type v) [Fintype ι] (n : ι → ℤ), (∀ i, 0 < n i) →
    (∀ i j, i ≠ j → Int.gcd (n i) (n j) = 1) →
      ∀ x y : ℤ, (∀ i, n i ∣ x - y) ↔ (∏ i, n i) ∣ x - y

/-- The actual cofactors N/n_i are coprime to n_i, vanish modulo all
other n_j, and admit inverse coefficients t_i. -/
def CofactorData : Prop :=
  ∀ (ι : Type v) [Fintype ι] (n : ι → ℤ), (∀ i, 0 < n i) →
    (∀ i j, i ≠ j → Int.gcd (n i) (n j) = 1) →
      ∀ i, Int.gcd ((∏ j, n j) / n i) (n i) = 1 ∧
        (∀ j, j ≠ i → n j ∣ (∏ k, n k) / n i) ∧
        ∃ t : ℤ, n i ∣ t * ((∏ j, n j) / n i) - 1

/-- For every valid choice of inverse coefficients, the displayed sum
has the prescribed residues. -/
def ExplicitSolution : Prop :=
  ∀ (ι : Type v) [Fintype ι] (n : ι → ℤ), (∀ i, 0 < n i) →
    (∀ i j, i ≠ j → Int.gcd (n i) (n j) = 1) →
      ∀ t : ι → ℤ, (∀ i, n i ∣ t i * ((∏ j, n j) / n i) - 1) →
        ∀ a : ι → ℤ, ∀ i,
          n i ∣ (∑ j, a j * t j * ((∏ k, n k) / n j)) - a i

end Specs.D07.Ch09.CrtFiniteInteger
