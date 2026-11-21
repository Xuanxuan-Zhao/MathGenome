import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! Independent type and value specifications for the binomial quantities.

These declarations assert no summability or coefficient estimates. In particular,
the tail definitions are genuine `tsum`s, with convergence left to later goals.
-/

noncomputable section
open scoped BigOperators

namespace D03SupportRepairs.Specs

def uType : Type := ℕ → ℝ

/-- The binomial sequence, totalized at zero. -/
def uValue (N : ℕ) : ℝ :=
  (1 + 1 / (N : ℝ)) ^ N

def bType : Type := ℕ → ℕ → ℝ

/-- The normalized canonical binomial coefficient. -/
def bValue (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) / (N : ℝ) ^ j

def prefixType : Type := ℕ → ℕ → ℝ

/-- The prefix through the inclusive cutoff J. -/
def prefixValue (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), bValue N j

def invFactorialType : Type := ℕ → ℝ

/-- The real inverse factorial. -/
def invFactorialValue (j : ℕ) : ℝ :=
  1 / (Nat.factorial j : ℝ)

def geomTermType : Type := ℕ → ℝ

/-- The source geometric majorant term. -/
def geomTermValue (j : ℕ) : ℝ :=
  (2 : ℝ) * (1 / 2 : ℝ) ^ j

def factorialTailType : Type := ℕ → ℝ

/-- The actual inverse-factorial series restricted to j > J. -/
def factorialTailValue (J : ℕ) : ℝ :=
  ∑' j : ℕ, if J < j then invFactorialValue j else 0

def geometricTailType : Type := ℕ → ℝ

/-- The actual geometric series restricted to j > J. -/
def geometricTailValue (J : ℕ) : ℝ :=
  ∑' j : ℕ, if J < j then geomTermValue j else 0

end D03SupportRepairs.Specs
