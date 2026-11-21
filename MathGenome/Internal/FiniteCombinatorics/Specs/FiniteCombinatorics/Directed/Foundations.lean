import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Zip

/-!
# Shared finite directed graphs: independent data and specification

Source: `paper.tex`, scope conventions, W17 (including its empty-walk convention),
W23, and the original-arc convention of W44 and W47.

`Digraph`, `Arc`, and `Walk` are the canonical shared data types. They are
placed in this independent module so every consumer uses the same objects.
No simplicity, loop-freeness, or injectivity of the endpoint maps is imposed.
The definitions in `Spec` specify the remaining public operations, without
importing their implementation.
-/

open scoped BigOperators

universe u v r

namespace FiniteCombinatorics.Directed

/-- A finite directed multigraph with a specified type of original arc identities.
The vertex and arc types may be empty. -/
structure Digraph (V : Type u) (A : Type v) [Fintype V] [Fintype A] where
  tail : A → V
  head : A → V

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- An original arc together with both of its incidence equations. -/
def Arc (G : Digraph V A) (x y : V) :=
  {a : A // G.tail a = x ∧ G.head a = y}

/-- Finite directed walks, indexed by their actual endpoints. Each step records
an original arc and its incidence data. -/
inductive Walk (G : Digraph V A) : V → V → Type (max u v)
  | nil (x : V) : Walk G x x
  | cons {x y z : V} (a : Arc G x y) (p : Walk G y z) : Walk G x z

noncomputable instance (G : Digraph V A) (x y : V) : Fintype (Arc G x y) :=
  by
    classical
    unfold Arc
    infer_instance

namespace Spec

/-- Original arcs in traversal order, including multiplicities. -/
def arcs {G : Digraph V A} {x y : V} : Walk G x y → List A
  | .nil _ => []
  | .cons a p => a.val :: arcs p

/-- The vertex sequence includes both endpoints, also for an empty walk. -/
def vertices {G : Digraph V A} {x y : V} : Walk G x y → List V
  | .nil x => [x]
  | .cons (x := x) _ p => x :: vertices p

def length {G : Digraph V A} {x y : V} (p : Walk G x y) : ℕ :=
  (arcs p).length

/-- Concatenation is defined only when the endpoints match. -/
def append {G : Digraph V A} {x y z : V} :
    Walk G x y → Walk G y z → Walk G x z
  | .nil _, q => q
  | .cons a p, q => .cons a (append p q)

/-- The one-step walk on an original arc, including a loop. -/
def single (G : Digraph V A) (a : A) : Walk G (G.tail a) (G.head a) :=
  .cons ⟨a, rfl, rfl⟩ (.nil _)

def isPath {G : Digraph V A} {x y : V} (p : Walk G x y) : Prop :=
  (vertices p).Nodup

def path (G : Digraph V A) (x y : V) :=
  {p : Walk G x y // isPath p}

def isClosed {G : Digraph V A} {x y : V} (_ : Walk G x y) : Prop := x = y

/-- Closed walks based at a specified vertex. -/
def closedWalk (G : Digraph V A) (x : V) := Walk G x x

/-- A simple directed cycle is nonempty and has no repeated vertices except
for the last occurrence of its base vertex. In particular a loop is a cycle. -/
def isCycle {G : Digraph V A} {x : V} (p : Walk G x x) : Prop :=
  0 < length p ∧ (vertices p).dropLast.Nodup

/-- Cycles retain a base vertex and original arc identities; rotations need
not be identified for the uses in circulation decompositions. -/
def cycle (G : Digraph V A) := Σ x : V, {p : Walk G x x // isCycle p}

/-- No simple directed cycle, including a one-arc loop. -/
def acyclic (G : Digraph V A) : Prop :=
  ∀ (x : V) (p : Walk G x x), ¬ isCycle p

def reachable (G : Digraph V A) (x y : V) : Prop := Nonempty (Walk G x y)

/-- Finite product in a commutative monoid; a commutative ring is a
special case. The empty product is one. -/
def weight {R : Type r} [CommMonoid R] {G : Digraph V A}
    (w : A → R) {x y : V} (p : Walk G x y) : R :=
  ((arcs p).map w).prod

/-- Real divergence of arbitrary arc loads. There are no capacities,
nonnegativity hypotheses, or distinguished source or sink in this definition.
A loop occurs in both sums with the same load. -/
noncomputable def divergence (G : Digraph V A) (f : A → ℝ) (x : V) : ℝ := by
  classical
  exact (∑ a ∈ Finset.univ.filter (fun a => G.tail a = x), f a) -
    ∑ a ∈ Finset.univ.filter (fun a => G.head a = x), f a

-- Full types and values for the public definitions.
section ExpectedTypes
set_option linter.checkUnivs false
set_option linter.unusedVariables false
def arcsType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y : V}, Walk G x y → List A

def verticesType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y : V}, Walk G x y → List V

def lengthType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y : V}, Walk G x y → ℕ

def appendType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y z : V}, Walk G x y → Walk G y z → Walk G x z

def singleType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (a : A), Walk G (G.tail a) (G.head a)

def isPathType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y : V}, Walk G x y → Prop

def pathType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (x y : V), Type (max u v)

def isClosedType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y : V}, Walk G x y → Prop

def closedWalkType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (x : V), Type (max u v)

def isCycleType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x : V}, Walk G x x → Prop

def cycleType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A), Type (max u v)

def acyclicType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A), Prop

def reachableType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (x y : V), Prop

def weightType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {R : Type r} [CommMonoid R] {G : Digraph V A} (w : A → R)
  {x y : V}, Walk G x y → R

def divergenceType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (f : A → ℝ) (x : V), ℝ

end ExpectedTypes

-- Independent specifications for the basic interface laws.
def arcs_append : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y z : V} (p : Walk G x y) (q : Walk G y z),
  arcs (append p q) = arcs p ++ arcs q

def length_append : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y z : V} (p : Walk G x y) (q : Walk G y z),
  length (append p q) = length p + length q

def vertices_append : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y z : V} (p : Walk G x y) (q : Walk G y z),
  vertices (append p q) = (vertices p).dropLast ++ vertices q

def length_vertices : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y : V} (p : Walk G x y),
  (vertices p).length = length p + 1

def incidence : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y : V} (p : Walk G x y),
  (arcs p).map (fun a => (G.tail a, G.head a)) =
    (vertices p).zip (vertices p).tail

def weight_nil : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {R : Type r} [CommMonoid R] (w : A → R) (x : V),
  weight w (Walk.nil (G := G) x) = 1

def weight_append : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {x y z : V} {R : Type r} [CommMonoid R] (w : A → R)
  (p : Walk G x y) (q : Walk G y z),
  weight w (append p q) = weight w p * weight w q

def nil_isPath : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (x : V), isPath (Walk.nil (G := G) x)

def nil_not_isCycle : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (x : V), ¬ isCycle (Walk.nil (G := G) x)

def loop_isCycle : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (x : V) (a : Arc G x x),
  isCycle (Walk.cons a (Walk.nil x))

end Spec
end FiniteCombinatorics.Directed
