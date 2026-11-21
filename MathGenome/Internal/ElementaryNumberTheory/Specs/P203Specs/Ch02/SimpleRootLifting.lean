import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic

/-! Independent statements for paper.tex:602–633, Theorem 2.6 (nt:B05).
A positive prime integer is represented by a natural prime cast to ℤ.
Congruences use divisibility of the difference, including negative representatives.
The sequence index n corresponds to modulus p^(n+1), so index zero is modulo p.
-/
namespace P203Specs.Ch02

/-- The displayed p representatives are distinct and exhaust precisely the fibre
of reduction from modulus p^(j+1) to the given class modulo p^j. -/
def PrimePowerFibre : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (j : ℕ), 1 ≤ j → ∀ a : ℤ,
    (∀ t s : Fin p,
      ((p : ℤ)^(j+1) ∣ (a+(p : ℤ)^j*(t.val : ℤ))-
        (a+(p : ℤ)^j*(s.val : ℤ))) ↔ t=s) ∧
    (∀ b : ℤ, (p : ℤ)^j ∣ b-a →
      ∃ t : Fin p, (p : ℤ)^(j+1) ∣ b-(a+(p : ℤ)^j*(t.val : ℤ)))

/-- Exactly one parameter class gives a root. Every integer in the original
fibre is a root precisely when it belongs to this one lifted class. The
lifted derivative has the original nonzero residue modulo p. -/
def SimpleRootStep : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (F : Polynomial ℤ) (j : ℕ), 1 ≤ j →
    ∀ a : ℤ, (p : ℤ)^j ∣ F.eval a → ¬(p : ℤ) ∣ F.derivative.eval a →
      ∃ t : Fin p,
        (p : ℤ)^(j+1) ∣ F.eval (a+(p : ℤ)^j*(t.val : ℤ)) ∧
        (p : ℤ) ∣ F.derivative.eval (a+(p : ℤ)^j*(t.val : ℤ))-
          F.derivative.eval a ∧
        ¬(p : ℤ) ∣ F.derivative.eval (a+(p : ℤ)^j*(t.val : ℤ)) ∧
        (∀ s : Fin p, ((p : ℤ)^(j+1) ∣
          F.eval (a+(p : ℤ)^j*(s.val : ℤ))) ↔ s=t) ∧
        (∀ b : ℤ, (p : ℤ)^j ∣ b-a →
          ((p : ℤ)^(j+1) ∣ F.eval b ↔
            (p : ℤ)^(j+1) ∣ b-(a+(p : ℤ)^j*(t.val : ℤ))))

/-- A compatible family over the particular given simple root a. At every
positive power, the last equivalence asserts uniqueness of the root class
among all classes reducing to a modulo p, as well as existence. -/
def SimpleRootTower : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (F : Polynomial ℤ) (a : ℤ),
    (p : ℤ) ∣ F.eval a → ¬(p : ℤ) ∣ F.derivative.eval a →
      ∃ r : ℕ → ℤ, r 0=a ∧
        (∀ n : ℕ, (p : ℤ)^(n+1) ∣ F.eval (r n) ∧
          (p : ℤ) ∣ r n-a ∧
          (p : ℤ) ∣ F.derivative.eval (r n)-F.derivative.eval a ∧
          ¬(p : ℤ) ∣ F.derivative.eval (r n)) ∧
        (∀ n : ℕ, (p : ℤ)^(n+1) ∣ r (n+1)-r n) ∧
        (∀ (n : ℕ) (b : ℤ), (p : ℤ) ∣ b-a →
          ((p : ℤ)^(n+1) ∣ F.eval b ↔ (p : ℤ)^(n+1) ∣ b-r n))

end P203Specs.Ch02
