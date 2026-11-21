import Mathlib.RingTheory.Polynomial.Content
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent statement of K07.13.irreducibility_test, paper.tex:4014–4023.
The fixed coefficient field K has q elements. Congruence modulo f means
equality of polynomial remainders. The gcd is the normalized (monic) gcd.
No extension field or identification of unrelated finite fields is used.
-/

universe u
namespace Specs.D07.Ch13.IrreducibilityTest

open Polynomial

/-- Rabin's criterion, including degree one, where the prime conditions
are vacuous. Natural-number division n / ℓ is exact because ℓ ∣ n. -/
def IrreducibilityCriterion : Prop := by
  classical
  exact ∀ (K : Type u) [Field K] [Finite K] (q n : ℕ),
    Nat.card K = q → 1 ≤ n → ∀ f : K[X], f.Monic → f.natDegree = n →
      (Irreducible f ↔
        (X ^ (q ^ n) : K[X]) % f = X % f ∧
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n →
          gcd f (X ^ (q ^ (n / ℓ)) - X) = 1)

end Specs.D07.Ch13.IrreducibilityTest
