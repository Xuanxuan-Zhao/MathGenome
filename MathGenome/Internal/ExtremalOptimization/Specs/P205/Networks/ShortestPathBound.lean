import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ShortestPathDistances
import Mathlib.Data.Fintype.Card

/-! W37 charging argument. Runs are arbitrary finite prefixes of the actual
full-bottleneck shortest-path rule, from any feasible real flow. Labels and
signs are retained, including when the original graph has parallel arcs. -/
open scoped Classical
universe u v
namespace P205.Networks.ShortestBoundSpec
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

def tail (G : Digraph V A) (r : A × Bool) : V :=
  if r.2 then G.tail r.1 else G.head r.1

def head (G : Digraph V A) (r : A × Bool) : V :=
  if r.2 then G.head r.1 else G.tail r.1

def reverse (r : A × Bool) : A × Bool := (r.1, !r.2)

/-- One actual augmentation, without an assumed saturation certificate. -/
structure AugmentationStep (N : Network V A) (f g : A → ℝ) where
  path : Walk (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f) N.source N.sink
  isPath : path.IsPath
  shortest : DistanceSpec.IsShortest path
  amount : ℝ
  bottleneck : BoundedSpec.Bottleneck N.graph (fun _ => 0) N.capacity f path amount
  update : g = BoundedSpec.augment N.graph (fun _ => 0) N.capacity f path amount

def Used {N : Network V A} {f g : A → ℝ}
    (S : AugmentationStep N f g) (r : A × Bool) : Prop :=
  r ∈ S.path.arcs.map Subtype.val

/-- A bottleneck copy selected on this step. Its disappearance is proved below. -/
def Saturates {N : Network V A} {f g : A → ℝ}
    (S : AugmentationStep N f g) (r : A × Bool) : Prop :=
  Used S r ∧ S.amount = BoundedSpec.capacity (fun _ => 0) N.capacity f r

/-- The natural-indexed flow outside the prefix is unrestricted. -/
structure Run (N : Network V A) (n : ℕ) where
  flow : ℕ → A → ℝ
  initial_feasible : N.Feasible (flow 0)
  step : ∀ i : Fin n, AugmentationStep N (flow i.val) (flow (i.val + 1))

noncomputable def level {N : Network V A} {n : ℕ} (R : Run N n) (i : ℕ) (x : V) : ℕ∞ :=
  DistanceSpec.distance (BoundedSpec.graph N.graph (fun _ => 0) N.capacity (R.flow i))
    N.source x

section Expected
set_option linter.checkUnivs false

def step_saturates : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f g : A → ℝ) (S : AugmentationStep N f g),
    ∃ r : A × Bool, Saturates S r ∧
      BoundedSpec.capacity (fun _ => 0) N.capacity g r = 0

/-- In fact this holds for any two saturations, hence for successive ones. -/
def repeated_saturation : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (n : ℕ) (R : Run N n) (i j : Fin n) (r : A × Bool),
    i.val < j.val → Saturates (R.step i) r → Saturates (R.step j) r →
    ∃ k : Fin n, i.val < k.val ∧ k.val < j.val ∧
      Used (R.step k) (reverse r) ∧
      level R i.val (tail N.graph r) + 2 ≤ level R k.val (tail N.graph r) ∧
      level R k.val (tail N.graph r) ≤ level R j.val (tail N.graph r)

def augmentation_bound : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (n : ℕ) (_R : Run N n),
    n ≤ 2 * Fintype.card V * Fintype.card A

end Expected
end P205.Networks.ShortestBoundSpec
