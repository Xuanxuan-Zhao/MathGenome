import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Data.List.Count
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent specification of paper.tex, W21 (Catalan family).
`DyckWord` requires equal U/D counts and count(D) ≤ count(U) in every
prefix. Its semilength is the number of U steps, not a separately assigned size.
Parenthesis words use a separate two-letter alphabet: opening means `(` and
closing means `)`. Balancedness means that every prefix has enough opening
parentheses, and that the full word has exactly n parentheses of each kind.
-/

namespace Specs.FiniteCombinatorics.Classes.Catalan

abbrev DyckPath (n : ℕ) := {p : DyckWord // p.semilength = n}

inductive Parenthesis
  | opening
  | closing
  deriving DecidableEq

/-- Replace an up step by `(` and a down step by `)`. -/
def parenthesisLetter : DyckStep ≃ Parenthesis where
  toFun s := match s with
    | .U => .opening
    | .D => .closing
  invFun s := match s with
    | .opening => .U
    | .closing => .D
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

def BalancedParenthesis (n : ℕ) :=
  {w : List Parenthesis //
    w.count .opening = n ∧ w.count .closing = n ∧
      ∀ i : ℕ, (w.take i).count .closing ≤ (w.take i).count .opening}

/-- Actual cardinality of the words, rather than a recursively defined sequence. -/
noncomputable def C (n : ℕ) : ℕ := Nat.card (DyckPath n)

noncomputable def B (n : ℕ) : ℕ := Nat.card (BalancedParenthesis n)

/-- Explicit count, length, and signed prefix-height interpretation. -/
def PathConditions : Prop := ∀ n (p : DyckPath n),
  p.val.toList.count .U = n ∧ p.val.toList.count .D = n ∧
    p.val.toList.length = 2 * n ∧
      ∀ i : ℕ, (0 : ℤ) ≤
        ((p.val.toList.take i).count .U : ℤ) - (p.val.toList.take i).count .D

/-- The bijection must act by replacing each individual letter. -/
def ParenthesisBijection : Prop := ∀ n,
  ∃ e : DyckPath n ≃ BalancedParenthesis n,
    ∀ p, (e p).val = p.val.toList.map parenthesisLetter

def ParenthesisFinite : Prop := ∀ n, Finite (BalancedParenthesis n)

def CommonCount : Prop := ∀ n, C n = B n

def CountZero : Prop := C 0 = 1

def CountRecurrence : Prop := ∀ n,
  C (n + 1) = ∑ i ∈ Finset.range (n + 1), C i * C (n - i)

def CountFormula : Prop := ∀ n, C n = Nat.choose (2 * n) n / (n + 1)

/-- This identity also certifies exact divisibility in the quotient formula. -/
def CountMultiplication : Prop := ∀ n, (n + 1) * C n = Nat.choose (2 * n) n

/-- Semilength zero includes exactly the empty word, in both representations. -/
def EmptyWords : Prop :=
  (∃ p : DyckPath 0, p.val.toList = []) ∧
  (∀ p : DyckPath 0, p.val.toList = []) ∧
  (∃ w : BalancedParenthesis 0, w.val = []) ∧
  (∀ w : BalancedParenthesis 0, w.val = [])

end Specs.FiniteCombinatorics.Classes.Catalan
