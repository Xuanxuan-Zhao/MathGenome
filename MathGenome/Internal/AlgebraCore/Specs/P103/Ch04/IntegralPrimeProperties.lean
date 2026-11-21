import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Field.IsField

/-!
Independent statements for the first two assertions of Theorem 4.7
(`paper.tex`, `p103:ALG-05-C01-S04`). Rings and maps are commutative
and unital. Prime and maximal ideals are proper, as in Mathlib.
The main assertions allow zero rings and arbitrary, possibly noninjective,
structure maps. The domain hypothesis belongs only to the field criterion.
-/

namespace P103.Ch04.IntegralPrimeProperties.Specs

universe u v

/-- A prime is maximal exactly when its contraction along an integral map is maximal. -/
def maximal_iff_contraction_maximal : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral → ∀ (q : Ideal A), q.IsPrime →
      (q.IsMaximal ↔ (q.comap g).IsMaximal)

/-- Comparable primes with the same contraction along an integral map coincide. -/
def incomparability : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral → ∀ (q q' : Ideal A),
      q.IsPrime → q'.IsPrime → q ≤ q' → q.comap g = q'.comap g → q = q'

/-- The field criterion used on integral inclusions of residue domains. -/
def domain_integral_over_field : Prop :=
  ∀ (K : Type u) (D : Type v) [CommRing K] [CommRing D] [IsDomain D]
    [Algebra K D], IsField K → (∀ x : D, IsIntegral K x) → IsField D

end P103.Ch04.IntegralPrimeProperties.Specs
