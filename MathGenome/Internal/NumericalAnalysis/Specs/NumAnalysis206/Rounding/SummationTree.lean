import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Operations
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.GammaProducts
import Mathlib.Data.List.OfFn
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! W08, summation-tree assertions (paper.tex 284–308).
The tree shape is independent of its labels. Empty trees return zero, leaves
are copied by `eval` through the supplied leaf map, and each branch executes
exactly one rounded addition. `depth` counts additions on the longest path.
`Nat.clog 2 n` is the ceiling logarithm; `Real.natCeil_logb_natCast` identifies
it with the real-log notation in the source. The other W08 assertions about
conditioning and matrix products belong to their separately allocated goals.
-/
namespace NumAnalysis206.Rounding

inductive AddTree (α : Type) where
  | empty
  | leaf (a : α)
  | branch (left right : AddTree α)
  deriving Inhabited

namespace AddTree

def leaves {α : Type} : AddTree α → List α
  | .empty => []
  | .leaf a => [a]
  | .branch l r => l.leaves ++ r.leaves

def depth {α : Type} : AddTree α → ℕ
  | .empty => 0
  | .leaf _ => 0
  | .branch l r => max l.depth r.depth + 1

def eval {α : Type} (round : ℝ → ℝ) (value : α → ℝ) : AddTree α → ℝ
  | .empty => 0
  | .leaf a => value a
  | .branch l r => round (eval round value l + eval round value r)

def exactSum {α : Type} (value : α → ℝ) : AddTree α → ℝ
  | .empty => 0
  | .leaf a => value a
  | .branch l r => exactSum value l + exactSum value r

def mass {α : Type} (value : α → ℝ) : AddTree α → ℝ
  | .empty => 0
  | .leaf a => |value a|
  | .branch l r => mass value l + mass value r

/-- Range checks on precisely the executed additions. -/
def Safe {α : Type} (round : ℝ → ℝ) (D : Set ℝ) (value : α → ℝ) :
    AddTree α → Prop
  | .empty => True
  | .leaf _ => True
  | .branch l r => Safe round D value l ∧ Safe round D value r ∧
      eval round value l + eval round value r ∈ D

def AllLeaves {α : Type} (p : α → Prop) : AddTree α → Prop
  | .empty => True
  | .leaf a => p a
  | .branch l r => AllLeaves p l ∧ AllLeaves p r

/-- The recursive equal-halves notion used in the source construction. -/
def Balanced {α : Type} : AddTree α → Prop
  | .empty => True
  | .leaf _ => True
  | .branch l r => Balanced l ∧ Balanced r ∧
      l.leaves.length ≤ r.leaves.length + 1 ∧
      r.leaves.length ≤ l.leaves.length + 1

end AddTree

namespace TreeSpecs

/-- Full bound for every supplied tree and every conservative path bound. -/
def sumError : Prop := ∀ (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (t : AddTree ℝ) (d : ℕ),
  Specs.RelativeModelValue round u D →
  Specs.NumAnalysis206.Rounding.budgetDomainValue d u →
  t.depth ≤ d → t.Safe round D id →
  |t.eval round id - t.exactSum id| ≤
    Specs.NumAnalysis206.Rounding.gammaValue d u * t.mass id

/-- Arbitrary ordered input values are preserved, including duplicates. -/
def balancedExistence : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (x : Fin n → ℝ),
  ∃ t : AddTree ℝ, t.leaves = List.ofFn x ∧ t.Balanced ∧
    t.depth ≤ ⌈Real.logb 2 (n : ℝ)⌉₊

/-- Each leaf executes an independent product rounding; additions then use the
stored products. All products and additions retain their own safety checks.
The required smallness condition is `(d+1)*u < 1`. -/
def productError : Prop := ∀ (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (t : AddTree (ℝ × ℝ)) (d : ℕ),
  Specs.RelativeModelValue round u D →
  Specs.NumAnalysis206.Rounding.budgetDomainValue (d + 1) u →
  t.depth ≤ d →
  t.AllLeaves (fun a => a.1 * a.2 ∈ D) →
  t.Safe round D (fun a => round (a.1 * a.2)) →
  |t.eval round (fun a => round (a.1 * a.2)) -
    t.exactSum (fun a => a.1 * a.2)| ≤
    Specs.NumAnalysis206.Rounding.gammaValue (d + 1) u *
      t.mass (fun a => a.1 * a.2)

def emptySum : Prop := ∀ (round : ℝ → ℝ),
  (AddTree.empty : AddTree ℝ).eval round id = 0 ∧
  (AddTree.empty : AddTree (ℝ × ℝ)).eval round (fun a => round (a.1 * a.2)) = 0

def leafCopy : Prop := ∀ (round : ℝ → ℝ) (x : ℝ),
  (AddTree.leaf x).eval round id = x ∧ (AddTree.leaf x).depth = 0

/-- Identification of the recursive exact quantities with the leaf sums in W08. -/
def exactQuantities : Prop := ∀ {α : Type} (t : AddTree α) (value : α → ℝ),
  t.exactSum value = (t.leaves.map value).sum ∧
  t.mass value = (t.leaves.map (fun a => |value a|)).sum

end TreeSpecs
end NumAnalysis206.Rounding
