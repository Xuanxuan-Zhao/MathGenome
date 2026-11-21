import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.Lagrange

/-! Independent specification of the divided-difference part of W48.
Lists contain node-value pairs. Distinctness concerns the nodes, not merely
pairs. The empty-list value is a convention; the coefficient theorem concerns
nonempty lists and uses the coefficient at length minus one, even if it is zero. -/

noncomputable section
open Polynomial
universe u
namespace Specs.NumAnalysis206.Approximation
variable {K : Type u} [Field K]
local instance : DecidableEq (K × K) := Classical.decEq _

/-- The recursive divided difference; no distinctness is needed to define it. -/
def dividedDifferenceValue : List (K × K) → K
  | [] => 0
  | [a] => a.2
  | a :: b :: l =>
      (dividedDifferenceValue (b :: l) - dividedDifferenceValue (a :: (b :: l).dropLast)) /
        (((b :: l).getLastD b).1 - a.1)
termination_by l => l.length

/-- The previously specified Lagrange interpolant, indexed by the node-value pairs. -/
def listInterpolantValue (l : List (K × K)) : K[X] := by
  classical
  exact interpolantValue l.toFinset Prod.fst Prod.snd

def dividedDifferenceType := ∀ {K : Type u} [Field K], List (K × K) → K
def listInterpolantType := ∀ {K : Type u} [Field K], List (K × K) → K[X]

def dividedDifferenceSingleton : Prop :=
  ∀ {K : Type u} [Field K] (a : K × K), dividedDifferenceValue [a] = a.2

def dividedDifferenceRecursion : Prop :=
  ∀ {K : Type u} [Field K] (a b : K × K) (l : List (K × K)),
    dividedDifferenceValue (a :: (l ++ [b])) =
      (dividedDifferenceValue (l ++ [b]) - dividedDifferenceValue (a :: l)) / (b.1 - a.1)

def listInterpolantEval : Prop :=
  ∀ {K : Type u} [Field K] (l : List (K × K)), (l.map Prod.fst).Nodup →
    ∀ a ∈ l, (listInterpolantValue l).eval a.1 = a.2

def listInterpolantDegree : Prop :=
  ∀ {K : Type u} [Field K] (l : List (K × K)), (l.map Prod.fst).Nodup →
    (listInterpolantValue l).degree < (l.length : WithBot ℕ)

def dividedDifferenceCoeff : Prop :=
  ∀ {K : Type u} [Field K] (l : List (K × K)), l ≠ [] →
    (l.map Prod.fst).Nodup →
    dividedDifferenceValue l = (listInterpolantValue l).coeff (l.length - 1)

def dividedDifferenceLowerDegree : Prop :=
  ∀ {K : Type u} [Field K] (l : List (K × K)), l ≠ [] →
    (l.map Prod.fst).Nodup →
    (listInterpolantValue l).degree < ((l.length - 1 : ℕ) : WithBot ℕ) →
    dividedDifferenceValue l = 0

def dividedDifferencePerm : Prop :=
  ∀ {K : Type u} [Field K] (l m : List (K × K)), l ≠ [] →
    (l.map Prod.fst).Nodup → l.Perm m →
    dividedDifferenceValue l = dividedDifferenceValue m

end Specs.NumAnalysis206.Approximation
