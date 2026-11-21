import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.PermutationCycles
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
Independent statements for the first Stirling array in paper.tex, W05.
The finite permutation statistic is the shared total count of complete cyclic
orbits, which includes every singleton fixed point.  The array is defined by
counting permutations; its identification with the recursive Mathlib array is
an obligation rather than an assumption.
-/
namespace FiniteCombinatorics.StirlingFirstSpec

universe u

/-- Cardinality of the permutations with exactly `k` complete cycles. -/
noncomputable def count (X : Type u) [Fintype X] (k : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Equiv.Perm X)).filter
    (fun σ => PermutationCyclesSpec.totalCycles σ = k)).card

/-- The unsigned first Stirling number, with its counting definition. -/
noncomputable def stirlingFirst (n k : ℕ) : ℕ := count (Fin n) k

def CountType := (X : Type u) → [Fintype X] → ℕ → ℕ
def StirlingFirstType := ℕ → ℕ → ℕ

/-- The complete permutation count agrees with the standard recursive array. -/
def CountInterpretation : Prop :=
  ∀ {X : Type u} [Fintype X] (k : ℕ),
    count X k = Nat.stirlingFirst (Fintype.card X) k

/-- The count depends only on the size of the finite set. -/
def FiniteTypeCount : Prop :=
  ∀ {X : Type u} [Fintype X] (k : ℕ),
    count X k = stirlingFirst (Fintype.card X) k

def RecursiveArray : Prop :=
  ∀ n k : ℕ, stirlingFirst n k = Nat.stirlingFirst n k

def ZeroZero : Prop := stirlingFirst 0 0 = 1

def EmptyPositive : Prop := ∀ k : ℕ, stirlingFirst 0 (k + 1) = 0

def PositiveZero : Prop := ∀ n : ℕ, stirlingFirst (n + 1) 0 = 0

def OutOfRange : Prop := ∀ n k : ℕ, n < k → stirlingFirst n k = 0

/-- The successor form avoids a truncated subtraction at `k = 0`. -/
def Recurrence : Prop := ∀ n k : ℕ,
  stirlingFirst (n + 1) (k + 1) = stirlingFirst n k + n * stirlingFirst n (k + 1)

end FiniteCombinatorics.StirlingFirstSpec
