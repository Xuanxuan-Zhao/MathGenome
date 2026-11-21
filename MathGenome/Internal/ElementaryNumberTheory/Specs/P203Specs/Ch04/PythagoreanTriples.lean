import Mathlib.Data.Int.GCD

/-! Independent statements for paper.tex, Theorem 4.1 [nt:D01].
All variables are integers; gcd is the nonnegative integer gcd. -/
namespace P203Specs.Ch04

/-- The positive parameters in the fixed odd-leg/even-leg order. -/
def Parameters (a b c r s : ℤ) : Prop :=
  0 < s ∧ s < r ∧ a = r ^ 2 - s ^ 2 ∧ b = 2 * r * s ∧
    c = r ^ 2 + s ^ 2 ∧ Int.gcd r s = 1 ∧ r % 2 ≠ s % 2

/-- Classification with the odd leg first, including uniqueness of the pair. -/
def FixedOrderClassification : Prop :=
  ∀ a b c : ℤ, 0 < a → 0 < b → 0 < c →
    a ^ 2 + b ^ 2 = c ^ 2 → Int.gcd a b = 1 → a % 2 = 1 →
      ∃! p : ℤ × ℤ, Parameters a b c p.1 p.2

/-- Exactly one leg is even, and exactly one of the two interchanges gives
an odd first leg, an even second leg, and the unique positive parameter pair. -/
def PrimitiveClassification : Prop :=
  ∀ a b c : ℤ, 0 < a → 0 < b → 0 < c →
    a ^ 2 + b ^ 2 = c ^ 2 → Int.gcd a b = 1 →
      ((a % 2 = 0 ∧ b % 2 = 1) ∨ (a % 2 = 1 ∧ b % 2 = 0)) ∧
      ∃! swap : Bool,
        let x := if swap then b else a
        let y := if swap then a else b
        x % 2 = 1 ∧ y % 2 = 0 ∧
          ∃! p : ℤ × ℤ, Parameters x y c p.1 p.2

/-- Every coprime positive ordered pair of opposite parity gives a positive
primitive Pythagorean triple in the fixed leg order. -/
def ParametrizationConverse : Prop :=
  ∀ r s : ℤ, 0 < s → s < r → Int.gcd r s = 1 → r % 2 ≠ s % 2 →
    let a := r ^ 2 - s ^ 2
    let b := 2 * r * s
    let c := r ^ 2 + s ^ 2
    0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧
      Int.gcd a b = 1 ∧ a % 2 = 1 ∧ b % 2 = 0

end P203Specs.Ch04
