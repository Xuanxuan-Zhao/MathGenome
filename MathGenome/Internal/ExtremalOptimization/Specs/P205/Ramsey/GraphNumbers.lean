import MathGenome.Internal.ExtremalOptimization.Specs.P205.Ramsey.Finite
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Choose.Basic

universe u

namespace P205.Ramsey

/-- All edges within `t` have the specified color. Extra edges outside `t`
are unrestricted: this is a non-induced monochromatic clique. -/
def ColoredClique {X : Type*} (c : KSubsets X 2 → Fin 2)
    (d : Fin 2) (t : Finset X) : Prop :=
  ∀ s : KSubsets X 2, s.val ⊆ t → c s = d

/-- The two asymmetric clique sizes, on every finite ground set of size `n`.
Color zero is red and color one is blue. -/
def GraphRamseyProperty (a b n : ℕ) : Prop :=
  ∀ (X : Type) (S : Finset X), S.card = n →
    ∀ c : KSubsets X 2 → Fin 2,
      (∃ t : Finset X, t ⊆ S ∧ t.card = a ∧ ColoredClique c 0 t) ∨
      (∃ t : Finset X, t ⊆ S ∧ t.card = b ∧ ColoredClique c 1 t)

namespace Specs

def RamseyNumberType := ℕ → ℕ → ℕ

/-- Infimum on naturals, with value zero if the set is empty. Existence and
positivity for positive parameters are proved separately. -/
noncomputable def ramseyNumberValue (a b : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ GraphRamseyProperty a b n}

def GraphRamseyExists : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ∃ n : ℕ, 0 < n ∧ GraphRamseyProperty a b n

def GraphRamseyMono : Prop :=
  ∀ a b n N : ℕ, GraphRamseyProperty a b n → n ≤ N → GraphRamseyProperty a b N

def RamseyNumberSpec : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    0 < ramseyNumberValue a b ∧ GraphRamseyProperty a b (ramseyNumberValue a b)

def RamseyNumberLeast : Prop :=
  ∀ a b n : ℕ, 0 < n → GraphRamseyProperty a b n → ramseyNumberValue a b ≤ n

def RamseyNumberThreshold : Prop :=
  ∀ a b n : ℕ, 1 ≤ a → 1 ≤ b → 0 < n →
    (GraphRamseyProperty a b n ↔ ramseyNumberValue a b ≤ n)

/-- The canonical number works on arbitrary finite ground sets in every universe. -/
def RamseyNumberOn : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ∀ (X : Type u) (S : Finset X), ramseyNumberValue a b ≤ S.card →
      ∀ c : KSubsets X 2 → Fin 2,
        (∃ t : Finset X, t ⊆ S ∧ t.card = a ∧ ColoredClique c 0 t) ∨
        (∃ t : Finset X, t ⊆ S ∧ t.card = b ∧ ColoredClique c 1 t)

def RamseyNumberOneLeft : Prop := ∀ b : ℕ, 1 ≤ b → ramseyNumberValue 1 b = 1

def RamseyNumberOneRight : Prop := ∀ a : ℕ, 1 ≤ a → ramseyNumberValue a 1 = 1

def RamseyNumberRecursion : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
    ramseyNumberValue a b ≤ ramseyNumberValue (a - 1) b + ramseyNumberValue a (b - 1)

def RamseyNumberBinomial : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ramseyNumberValue a b ≤ Nat.choose (a + b - 2) (a - 1)

end Specs
end P205.Ramsey
