import MathGenome.Internal.Specs.D07.Ch07.TorsionCountInvariants

/-!
Independent specification of K07.07.primary_cyclic_uniqueness,
paper.tex:3443–3450. Products are finite Cartesian products of the actual
additive cyclic groups ZMod n; a list with no entries gives the zero group.
Permutation of lists expresses equality of multisets, with multiplicity.
-/
namespace Specs.D07.Ch07.PrimaryCyclicUniqueness

open Specs.D07.Ch07.TorsionCountInvariants

/-- Each pair records the prime and its strictly positive exponent. -/
def ValidElementaryDivisors (d : List (ℕ × ℕ)) : Prop :=
  ∀ a ∈ d, a.1.Prime ∧ 0 < a.2

/-- Prime-labelled cyclic factors, allowing repeated primes and exponents. -/
abbrev ElementaryProduct (d : List (ℕ × ℕ)) :=
  (i : Fin d.length) → ZMod ((d.get i).1 ^ (d.get i).2)

def PrimaryUniqueness : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (e f : List ℕ),
    (∀ n ∈ e, 0 < n) → (∀ n ∈ f, 0 < n) →
    (PrimePowerProduct p e ≃+ PrimePowerProduct p f) → e.Perm f

/-- Uniqueness retains the prime label as well as the exponent. -/
def ElementaryDivisorUniqueness : Prop :=
  ∀ (d e : List (ℕ × ℕ)), ValidElementaryDivisors d →
    ValidElementaryDivisors e →
    (ElementaryProduct d ≃+ ElementaryProduct e) → d.Perm e

/-- The same assertion for any two decompositions of a finite abelian group. -/
def FiniteAbelianUniqueness : Prop :=
  ∀ (A : Type*) [AddCommGroup A] [Finite A]
    (d e : List (ℕ × ℕ)), ValidElementaryDivisors d →
    ValidElementaryDivisors e →
    (A ≃+ ElementaryProduct d) → (A ≃+ ElementaryProduct e) →
    d.Perm e ∧
      (d.map fun a => a.1 ^ a.2).Perm (e.map fun a => a.1 ^ a.2)

end Specs.D07.Ch07.PrimaryCyclicUniqueness
