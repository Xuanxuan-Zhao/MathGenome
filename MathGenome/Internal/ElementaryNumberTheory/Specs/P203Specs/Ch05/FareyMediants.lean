import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval

/-! Independent specification for `paper.tex`, §5 Farey fractions,
lines 2300–2302 and 2312–2324. Denominators are positive integers;
numerators in the general mediant statements may be negative. -/
namespace P203Specs.Ch05

/-- A fraction is encoded by its integer numerator and denominator. -/
abbrev Fraction := ℤ × ℤ

def fractionValue (x : Fraction) : ℚ := (x.1 : ℚ) / (x.2 : ℚ)

def Reduced (x : Fraction) : Prop := 0 < x.2 ∧ Int.gcd x.1 x.2 = 1

/-- The finite Farey set, carrying the order induced by `fractionValue`.
For positive orders this contains exactly the reduced fractions in [0,1]. -/
def farey (N : ℤ) : Finset Fraction :=
  ((Finset.Icc 0 N).product (Finset.Icc 1 N)).filter
    (fun x => x.1 ≤ x.2 ∧ Int.gcd x.1 x.2 = 1)

/-- Ordered neighbors in the finite set; membership is part of the relation. -/
def orderedNeighbors (N : ℤ) (x y : Fraction) : Prop :=
  x ∈ farey N ∧ y ∈ farey N ∧ fractionValue x < fractionValue y ∧
    ∀ z ∈ farey N, ¬ (fractionValue x < fractionValue z ∧
      fractionValue z < fractionValue y)

abbrev FareyType := ℤ → Finset Fraction
abbrev OrderedNeighborsType := ℤ → Fraction → Fraction → Prop

def FareyMembership : Prop :=
  ∀ (N : ℤ) (x : Fraction), x ∈ farey N ↔
    Reduced x ∧ 0 ≤ fractionValue x ∧ fractionValue x ≤ 1 ∧ x.2 ≤ N

/-- Completeness of the pair encoding with respect to ordinary rationals
and their canonical positive reduced denominators. -/
def FareyRationalMembership : Prop :=
  ∀ (N : ℤ) (r : ℚ), (∃ x ∈ farey N, fractionValue x = r) ↔
    0 ≤ r ∧ r ≤ 1 ∧ (r.den : ℤ) ≤ N

def FareyEndpoints : Prop :=
  ∀ N : ℤ, 1 ≤ N → (0, 1) ∈ farey N ∧ (1, 1) ∈ farey N

def ReducedInjectivity : Prop :=
  ∀ x y : Fraction, Reduced x → Reduced y →
    fractionValue x = fractionValue y → x = y

def MediantReduced : Prop :=
  ∀ a b c d : ℤ, 0 < b → 0 < d → b*c-a*d = 1 →
    Reduced (a+c, b+d)

def MediantInterior : Prop :=
  ∀ a b c d : ℤ, 0 < b → 0 < d → b*c-a*d = 1 →
    fractionValue (a,b) < fractionValue (a+c,b+d) ∧
    fractionValue (a+c,b+d) < fractionValue (c,d)

def MediantDeterminants : Prop :=
  ∀ a b c d : ℤ, b*c-a*d = 1 →
    b*(a+c)-a*(b+d) = 1 ∧ (b+d)*c-(a+c)*d = 1

/-- The lower bound is valid even for unreduced interior fractions. -/
def InteriorDenominator : Prop :=
  ∀ a b c d p q : ℤ, 0 < b → 0 < d → 0 < q → b*c-a*d = 1 →
    fractionValue (a,b) < fractionValue (p,q) →
    fractionValue (p,q) < fractionValue (c,d) →
    b+d ≤ q ∧ (q = b+d ↔ p = a+c ∧ q = b+d)

/-- The mediant is the unique reduced interior fraction of least denominator,
with uniqueness of the integer coordinates, not only of its rational value. -/
def MediantUniqueMinimum : Prop :=
  ∀ a b c d : ℤ, Reduced (a,b) → Reduced (c,d) →
    fractionValue (a,b) < fractionValue (c,d) → b*c-a*d = 1 →
    ∃! x : Fraction,
      Reduced x ∧ fractionValue (a,b) < fractionValue x ∧
      fractionValue x < fractionValue (c,d) ∧
      ∀ y : Fraction, Reduced y →
        fractionValue (a,b) < fractionValue y →
        fractionValue y < fractionValue (c,d) → x.2 ≤ y.2

end P203Specs.Ch05
