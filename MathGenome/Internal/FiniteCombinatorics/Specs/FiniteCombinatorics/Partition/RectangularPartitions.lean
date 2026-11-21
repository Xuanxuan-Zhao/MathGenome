import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.Foundations
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
namespace FiniteCombinatorics.Partition.RectangleSpecs

/-- Bounds on the shared decreasing-list presentation of partitions. -/
def Admissible (a b : ℕ) (l : List ℕ) : Prop :=
  (∃ p : Specs.PartitionValue l.sum, p.val = l) ∧
    l.length ≤ a ∧ ∀ i ∈ l, i ≤ b

/-- Finite enumeration, with the empty partition included on both edges. -/
def ListsValue : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | _ + 1, 0 => {[]}
  | a + 1, b + 1 => ListsValue (a + 1) b ∪
      (ListsValue a (b + 1)).image (List.cons (b + 1))
termination_by a b => a + b

def ListsType := ℕ → ℕ → Finset (List ℕ)
def PolynomialType := ℕ → ℕ → Polynomial ℤ

def FValue (a b : ℕ) : Polynomial ℤ :=
  ∑ l ∈ ListsValue a b, Polynomial.X ^ l.sum

def GValue (n k : ℕ) : Polynomial ℤ :=
  if k ≤ n then FValue k (n - k) else 0

def Enumeration : Prop :=
  ∀ a b l, l ∈ ListsValue a b ↔ Admissible a b l

def FiniteIndex : Prop := ∀ a b, {l | Admissible a b l}.Finite

def Recurrence : Prop := ∀ a b, 0 < a → 0 < b →
  FValue a b = FValue a (b - 1) + Polynomial.X ^ b * FValue (a - 1) b

def Boundary : Prop :=
  (∀ a, FValue a 0 = 1) ∧ (∀ b, FValue 0 b = 1)

def GaussianRecurrence : Prop := ∀ n k,
  GValue (n + 1) (k + 1) = GValue n (k + 1) +
    Polynomial.X ^ (n - k) * GValue n k

def GaussianBoundary : Prop :=
  (∀ n, GValue n 0 = 1) ∧ (∀ n, GValue n n = 1) ∧
    (∀ n k, n < k → GValue n k = 0)

end FiniteCombinatorics.Partition.RectangleSpecs
