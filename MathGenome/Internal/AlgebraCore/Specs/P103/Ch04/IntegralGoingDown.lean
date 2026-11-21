import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Fin.Basic

/-!
Independent statements for the integral going-down assertion of Theorem 4.8
(`paper.tex:922–930`) and its finite-chain consequence (`paper.tex:932`).
The structure map is an injective integral homomorphism of commutative domains.
`IsIntegrallyClosed R` means integrally closed in `FractionRing R`; it imposes
no condition on the extension of fraction fields. Primes are proper. Chains
use non-strict inclusion, including repetitions and the zero-step case.
-/

namespace P103.Ch04.IntegralGoingDown.Specs

universe u v

/-- Lift a descending step from an arbitrary prescribed prime over its top. -/
def going_down : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [IsDomain R] [IsDomain A] [IsIntegrallyClosed R]
    (g : R →+* A), Function.Injective g → g.IsIntegral →
    ∀ (p p' : Ideal R) (q' : Ideal A),
      p.IsPrime → p'.IsPrime → q'.IsPrime →
      p ≤ p' → Ideal.comap g q' = p' →
      ∃ q : Ideal A, q ≤ q' ∧ q.IsPrime ∧ Ideal.comap g q = p

/-- Lift a finite descending chain with its initial (largest) prime prescribed.
`n` counts steps, so `n = 0` is a single prime. -/
def finite_chain_lift : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [IsDomain R] [IsDomain A] [IsIntegrallyClosed R]
    (g : R →+* A), Function.Injective g → g.IsIntegral →
    ∀ (n : ℕ) (p : Fin (n + 1) → Ideal R),
      (∀ i, (p i).IsPrime) → Antitone p →
      ∀ q₀ : Ideal A, q₀.IsPrime → Ideal.comap g q₀ = p 0 →
      ∃ q : Fin (n + 1) → Ideal A,
        q 0 = q₀ ∧ (∀ i, (q i).IsPrime) ∧ Antitone q ∧
          ∀ i, Ideal.comap g (q i) = p i

end P103.Ch04.IntegralGoingDown.Specs
