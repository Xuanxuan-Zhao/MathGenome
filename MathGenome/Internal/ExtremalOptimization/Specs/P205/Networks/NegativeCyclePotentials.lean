import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Defs

/-!
Finite labelled directed graphs. Arc labels are arbitrary elements of `E`;
the endpoint maps may have loops, parallel arcs, or opposite arcs.
-/
namespace P205.Networks

universe u v

/-- An edge list is a directed walk from `a` to `b`. The empty walk has
equal endpoints. No reachability or nonemptiness assumption is imposed. -/
def IsWalk {V : Type u} {E : Type v} (tail head : E → V) :
    V → List E → V → Prop
  | a, [], b => a = b
  | a, e :: es, b => tail e = a ∧ IsWalk tail head (head e) es b

/-- Total real cost, counting each occurrence of each labelled arc. -/
def walkCost {E : Type v} (cost : E → ℝ) (es : List E) : ℝ :=
  (es.map cost).sum

/-- A simple directed cycle has positive length and visits each vertex once
before returning to its start. In particular, a one-arc loop is a cycle. -/
def IsSimpleCycle {V : Type u} {E : Type v} (tail head : E → V)
    (a : V) (es : List E) : Prop :=
  IsWalk tail head a es a ∧ es ≠ [] ∧ (es.map tail).Nodup

/-- Absence of strictly negative simple directed cycles, including loops. -/
def NoNegativeSimpleCycles {V : Type u} {E : Type v} (tail head : E → V)
    (cost : E → ℝ) : Prop :=
  ∀ a es, IsSimpleCycle tail head a es → 0 ≤ walkCost cost es

/-- Full, independent specification of the finite labelled digraph criterion. -/
def NegativeCyclePotentialsStatement : Prop :=
  ∀ (V : Type u) (E : Type v) [Finite V] [Finite E]
    (tail head : E → V) (cost : E → ℝ),
    NoNegativeSimpleCycles tail head cost ↔
      ∃ π : V → ℝ, ∀ e, 0 ≤ cost e + π (tail e) - π (head e)

end P205.Networks
