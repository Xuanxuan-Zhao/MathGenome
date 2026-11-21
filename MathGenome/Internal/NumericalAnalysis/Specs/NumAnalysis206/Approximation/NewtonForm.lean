import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.DividedDifferences
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Independent specification of the Newton expansion and backward evaluation
in paper.tex W48. Lists contain (node,value) pairs; all fields, including fields
of positive characteristic, are allowed. Products use the ordered prefix itself,
so the product for k = 0 is the empty product. -/
noncomputable section
open Polynomial
universe u
namespace Specs.NumAnalysis206.Approximation
variable {K : Type u} [Field K]

def newtonProductValue (l : List (K × K)) (k : ℕ) : K[X] :=
  ((l.take k).map (fun a => X - C a.1)).prod

def newtonPolynomialValue (l : List (K × K)) : K[X] :=
  ∑ k ∈ Finset.range l.length,
    C (dividedDifferenceValue (l.take (k + 1))) * newtonProductValue l k

/-- The node lookup is only used at indices strictly below the list length. -/
def newtonNode (l : List (K × K)) (k : ℕ) : K := (l[k]?.getD (0, 0)).1

/-- Evaluate a block of `count` terms starting at `start`, from right to left.
The zero accumulator after the last term makes a one-term block equal c_start. -/
def backwardValue (x c : ℕ → K) (z : K) : ℕ → ℕ → K
  | _, 0 => 0
  | start, count + 1 => c start + (z - x start) * backwardValue x c z (start + 1) count

def newtonRValue (l : List (K × K)) (z : K) (k : ℕ) : K :=
  backwardValue (newtonNode l) (fun j => dividedDifferenceValue (l.take (j + 1)))
    z k (l.length - k)

def newtonProductType := ∀ {K : Type u} [Field K], List (K × K) → ℕ → K[X]
def newtonPolynomialType := ∀ {K : Type u} [Field K], List (K × K) → K[X]
def newtonRType := ∀ {K : Type u} [Field K], List (K × K) → K → ℕ → K

def newtonRepresentation : Prop :=
  ∀ {K : Type u} [Field K] (l : List (K × K)), (l.map Prod.fst).Nodup →
    listInterpolantValue l = newtonPolynomialValue l

def newtonEvaluation : Prop :=
  ∀ {K : Type u} [Field K] (l : List (K × K)), (l.map Prod.fst).Nodup →
    ∀ z : K, (listInterpolantValue l).eval z = newtonRValue l z 0

def newtonRLast : Prop :=
  ∀ {K : Type u} [Field K] (l : List (K × K)), l ≠ [] →
    ∀ z : K, newtonRValue l z (l.length - 1) = dividedDifferenceValue l

def newtonRStep : Prop :=
  ∀ {K : Type u} [Field K] (l : List (K × K)) (z : K) (k : ℕ),
    k + 1 < l.length →
    newtonRValue l z k = dividedDifferenceValue (l.take (k + 1)) +
      (z - newtonNode l k) * newtonRValue l z (k + 1)

def newtonProductZero : Prop :=
  ∀ {K : Type u} [Field K] (l : List (K × K)), newtonProductValue l 0 = 1

def newtonSingleton : Prop :=
  ∀ {K : Type u} [Field K] (a : K × K),
    newtonPolynomialValue [a] = C a.2 ∧ ∀ z : K, newtonRValue [a] z 0 = a.2

end Specs.NumAnalysis206.Approximation
