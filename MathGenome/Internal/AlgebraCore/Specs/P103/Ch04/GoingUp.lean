import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Fin.Basic

/-!
Independent statements for going up, Theorem 4.8, first assertion
(`paper.tex:919–926`), and its finite-chain consequence (`paper.tex:932`).
Rings are commutative and unital; zero rings and noninjective maps are allowed.
Contraction is ideal preimage. Chains use non-strict inclusion, so repetitions
and the chain consisting only of the designated initial prime are included.
-/

namespace P103.Ch04.GoingUp.Specs

universe u v

/-- Lift an inclusion of base primes from any specified prime above its start. -/
def going_up : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral →
    ∀ (p p' : Ideal R) (q : Ideal A),
      p.IsPrime → p'.IsPrime → q.IsPrime →
      p ≤ p' → Ideal.comap g q = p →
      ∃ q' : Ideal A, q ≤ q' ∧ q'.IsPrime ∧ Ideal.comap g q' = p'

/-- Lift every finite increasing chain, with the first upstairs prime prescribed.
`n` is the number of steps; `n = 0` gives a one-prime chain. -/
def finite_chain_lift : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), g.IsIntegral →
    ∀ (n : ℕ) (p : Fin (n + 1) → Ideal R),
      (∀ i, (p i).IsPrime) → Monotone p →
      ∀ q₀ : Ideal A, q₀.IsPrime → Ideal.comap g q₀ = p 0 →
      ∃ q : Fin (n + 1) → Ideal A,
        q 0 = q₀ ∧ (∀ i, (q i).IsPrime) ∧ Monotone q ∧
          ∀ i, Ideal.comap g (q i) = p i

end P103.Ch04.GoingUp.Specs
