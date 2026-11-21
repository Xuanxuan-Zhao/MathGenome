import MathGenome.Internal.Specs.D07.Ch10.GcdLcm
import MathGenome.Internal.Specs.D07.Ch10.UfdPrimeIrreducible
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Independent statements for K07.10.ufd_gcd, paper.tex:2029–2043.
The finite set `s` consists of prime representatives, pairwise nonassociated.
Exponents are natural numbers; an absent prime has exponent zero. Units in the
input factorizations are explicit. No normalization or GCD structure is assumed.
`IsGcd` and `IsLcm` are the upstream universal divisibility predicates.
-/

universe u

namespace Specs.D07.Ch10.UfdGcd

open Specs.D07.Ch10.GcdLcm

/-- A simultaneous choice of prime representatives and factorizations exists
for every pair of nonzero elements, including units (empty products). -/
def PrimePowerRepresentations : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a b : R), a ≠ 0 → b ≠ 0 →
    ∃ (s : Finset R) (e f : R → ℕ) (v w : Rˣ),
      (∀ p ∈ s, Prime p) ∧ (s : Set R).Pairwise (fun p q => ¬Associated p q) ∧
      (∀ p ∈ s, p ∣ a ∨ p ∣ b) ∧
      (∀ p ∉ s, e p = 0 ∧ f p = 0) ∧
      a = (v : R) * ∏ p ∈ s, p ^ e p ∧
      b = (w : R) * ∏ p ∈ s, p ^ f p

/-- Coordinatewise comparison holds for any choice of prime representatives
and any leading units, rather than just for a chosen normalization. -/
def DivisibilityByExponents : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (s : Finset R) (e f : R → ℕ) (a b : R) (v w : Rˣ),
    (∀ p ∈ s, Prime p) → (s : Set R).Pairwise (fun p q => ¬Associated p q) →
    a = (v : R) * ∏ p ∈ s, p ^ e p →
    b = (w : R) * ∏ p ∈ s, p ^ f p →
    (a ∣ b ↔ ∀ p ∈ s, e p ≤ f p)

def GcdFromMinimum : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (s : Finset R) (e f : R → ℕ) (a b : R) (v w : Rˣ),
    (∀ p ∈ s, Prime p) → (s : Set R).Pairwise (fun p q => ¬Associated p q) →
    a = (v : R) * ∏ p ∈ s, p ^ e p →
    b = (w : R) * ∏ p ∈ s, p ^ f p →
    IsGcd R a b (∏ p ∈ s, p ^ min (e p) (f p))

def LcmFromMaximum : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (s : Finset R) (e f : R → ℕ) (a b : R) (v w : Rˣ),
    (∀ p ∈ s, Prime p) → (s : Set R).Pairwise (fun p q => ¬Associated p q) →
    a = (v : R) * ∏ p ∈ s, p ^ e p →
    b = (w : R) * ∏ p ∈ s, p ^ f p →
    IsLcm R a b (∏ p ∈ s, p ^ max (e p) (f p))

/-- Compatible prime-power products satisfy an exact equality; the leading
units in the original inputs are why their product is only associated. -/
def MinMaxProduct : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (s : Finset R) (e f : R → ℕ),
    (∏ p ∈ s, p ^ min (e p) (f p)) * (∏ p ∈ s, p ^ max (e p) (f p)) =
      (∏ p ∈ s, p ^ e p) * (∏ p ∈ s, p ^ f p)

/-- This quantifies over all gcd and lcm choices and includes zero inputs. -/
def GcdLcmProductAssociation : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a b d m : R), IsGcd R a b d → IsLcm R a b m → Associated (d * m) (a * b)

def GcdLcmExistence : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a b : R), ∃ d m : R, IsGcd R a b d ∧ IsLcm R a b m ∧
      Associated (d * m) (a * b)

/-- The boundary case asserts that both products actually vanish. -/
def ZeroInputProducts : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b d m : R),
    (a = 0 ∨ b = 0) → IsGcd R a b d → IsLcm R a b m →
    d * m = 0 ∧ a * b = 0

end Specs.D07.Ch10.UfdGcd
