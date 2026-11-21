import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
Statements for the integer-scaling and prime-choice paragraphs of
`paper.tex:7685–7704` (the proof of `lem:lindemann-special-relation`).
A list records all complex roots, with repetitions. Rationality means an
actual rational polynomial whose complex coefficient map is the given product.
No nonemptiness or distinctness assumption is made on the list.
-/

namespace Specs.D07.Appendix.LindemannRelationIntegerScaling

open Polynomial

/-- A positive integer scales every root so that the monic root product is
an integer polynomial. Both the rational change-of-variable formula and the
complex factorization are retained, as is the nonzero constant coefficient. -/
def IntegerScaling : Prop :=
  ∀ (β : List ℂ) (P : ℚ[X]),
    (∀ b ∈ β, b ≠ 0) →
    P.map (algebraMap ℚ ℂ) = (β.map (fun b => X - C b)).prod →
    ∃ (a : ℤ) (Q : ℤ[X]),
      0 < a ∧ Q.Monic ∧ Q.coeff 0 ≠ 0 ∧ Q.natDegree = β.length ∧
      Q.map (algebraMap ℤ ℚ) =
        C ((a : ℚ) ^ β.length) * P.comp (C ((a : ℚ)⁻¹) * X) ∧
      Q.map (algebraMap ℤ ℂ) =
        (β.map (fun b => X - C ((a : ℂ) * b))).prod

/-- For each positive integer k and every size bound, a prime avoids the
fixed nonzero integer k*a*Q(0). The scale a is chosen independently of k. -/
def ArbitrarilyLargePrimes : Prop :=
  ∀ (k a : ℤ) (Q : ℤ[X]), 0 < k → 0 < a → Q.coeff 0 ≠ 0 →
    k * a * Q.coeff 0 ≠ 0 ∧
      ∀ B : ℕ, ∃ p : ℕ, B < p ∧ Nat.Prime p ∧ ¬ (p : ℤ) ∣ k * a * Q.coeff 0

end Specs.D07.Appendix.LindemannRelationIntegerScaling
