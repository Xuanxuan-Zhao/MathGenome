import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Data.ZMod.Basic

/-!
Independent specification of K07.15.cyclotomic_polynomials,
paper.tex:4337–4351 (including the following coefficient-field warning).

The source defines Φₙ as a product in ℂ[X]. `complexPrimitiveProduct`
retains that definition explicitly. `Polynomial.cyclotomic n ℤ` is its
integer realization, identified by a coefficient-map equality and uniqueness.
The rational and finite-field polynomials are coefficient images of that
same integer polynomial; irreducibility is asserted over ℚ and ℤ only.
All general assertions retain n ≥ 1, including n = 1.
-/

namespace Specs.D07.Ch15.CyclotomicPolynomials

open Polynomial

/-- The product in the original definition, with each primitive root once. -/
noncomputable def complexPrimitiveProduct (n : ℕ) : Polynomial ℂ :=
  ∏ ζ ∈ primitiveRoots n ℂ, (X - C ζ)

/-- The finite indexing set really contains all and only exact-order roots. -/
def PrimitiveRootsMeaning : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ ζ : ℂ,
    (ζ ∈ primitiveRoots n ℂ ↔ IsPrimitiveRoot ζ n)

def IntegerRealization : Prop :=
  ∀ (n : ℕ), 0 < n →
    (cyclotomic n ℤ).map (Int.castRingHom ℂ) = complexPrimitiveProduct n

/-- Membership in ℤ[X] is a conclusion; no integrality certificate is assumed. -/
def UniqueIntegerRealization : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∃! P : Polynomial ℤ, P.map (Int.castRingHom ℂ) = complexPrimitiveProduct n

def CoefficientCompatibility : Prop :=
  ∀ (n : ℕ), 0 < n →
    (cyclotomic n ℤ).map (algebraMap ℤ ℚ) = cyclotomic n ℚ ∧
    (cyclotomic n ℚ).map (algebraMap ℚ ℂ) = complexPrimitiveProduct n ∧
    (cyclotomic n ℤ).map (Int.castRingHom (ZMod 5)) = cyclotomic n (ZMod 5)

def Monicity : Prop :=
  ∀ (n : ℕ), 0 < n →
    (cyclotomic n ℤ).Monic ∧ (complexPrimitiveProduct n).Monic

/-- Both degree conventions are recorded; these polynomials are nonzero. -/
def Degree : Prop :=
  ∀ (n : ℕ), 0 < n →
    (cyclotomic n ℤ).degree = (Nat.totient n : WithBot ℕ) ∧
    (cyclotomic n ℤ).natDegree = Nat.totient n ∧
    (complexPrimitiveProduct n).degree = (Nat.totient n : WithBot ℕ) ∧
    (complexPrimitiveProduct n).natDegree = Nat.totient n

def DivisorFactorization : Prop :=
  ∀ (n : ℕ), 0 < n →
    (X ^ n - 1 : Polynomial ℤ) = ∏ d ∈ n.divisors, cyclotomic d ℤ

def ComplexDivisorFactorization : Prop :=
  ∀ (n : ℕ), 0 < n →
    (X ^ n - 1 : Polynomial ℂ) = ∏ d ∈ n.divisors, complexPrimitiveProduct d

def RationalIrreducibility : Prop :=
  ∀ (n : ℕ), 0 < n → Irreducible (cyclotomic n ℚ)

/-- The integral primitive-polynomial formulation in the source proof. -/
def IntegralIrreducibility : Prop :=
  ∀ (n : ℕ), 0 < n →
    (cyclotomic n ℤ).IsPrimitive ∧ Irreducible (cyclotomic n ℤ)

/-- Every primitive complex root, rather than just a chosen exponential root. -/
def MinimalPolynomial : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ ζ : ℂ, IsPrimitiveRoot ζ n →
    minpoly ℚ ζ = (cyclotomic n ℤ).map (algebraMap ℤ ℚ)

def FirstCyclotomic : Prop :=
  cyclotomic 1 ℤ = X - 1 ∧ complexPrimitiveProduct 1 = X - 1

def FourthCyclotomic : Prop :=
  cyclotomic 4 ℤ = X ^ 2 + 1 ∧
    complexPrimitiveProduct 4 = X ^ 2 + 1 ∧
    Irreducible (X ^ 2 + 1 : Polynomial ℚ)

def QuarticFactorization : Prop :=
  (X ^ 4 - 1 : Polynomial ℤ) = (X - 1) * (X + 1) * (X ^ 2 + 1)

def ModFiveFactorization : Prop :=
  cyclotomic 4 (ZMod 5) = X ^ 2 + 1 ∧
    (X ^ 2 + 1 : Polynomial (ZMod 5)) = (X - C 2) * (X + C 2)

/-- Both factors have positive degree and are nonunits; 5 does not divide 4. -/
def ModFiveReducibility : Prop :=
  (X - C 2 : Polynomial (ZMod 5)).degree = 1 ∧
    (X + C 2 : Polynomial (ZMod 5)).degree = 1 ∧
    ¬IsUnit (X - C 2 : Polynomial (ZMod 5)) ∧
    ¬IsUnit (X + C 2 : Polynomial (ZMod 5)) ∧
    ¬Irreducible (cyclotomic 4 (ZMod 5)) ∧ ¬(5 : ℕ) ∣ 4

end Specs.D07.Ch15.CyclotomicPolynomials
