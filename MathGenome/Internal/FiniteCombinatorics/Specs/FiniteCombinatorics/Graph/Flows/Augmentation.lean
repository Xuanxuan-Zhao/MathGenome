import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Independent specification of the first assertion of `p204:residual-path`.
The second (reachable-cut) assertion belongs to ResidualOptimality. Copies are
labelled by an original arc and a Boolean: true is forward, false is backward.
Only copies of strictly positive residual capacity are retained. -/

universe u v
namespace FiniteCombinatorics.Graph.Flows
open FiniteCombinatorics.Directed
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

namespace ResidualSpec

def capacity (N : Network V A) (f : A → ℝ) (b : A × Bool) : ℝ :=
  if b.2 then N.capacity b.1 - f b.1 else f b.1

end ResidualSpec

/-- Distinct tagged positive copies, even for parallel or opposite originals. -/
def Network.ResidualArc (N : Network V A) (f : A → ℝ) :=
  {b : A × Bool // 0 < ResidualSpec.capacity N f b}

noncomputable instance (N : Network V A) (f : A → ℝ) : Fintype (N.ResidualArc f) := by
  classical
  unfold Network.ResidualArc
  infer_instance

namespace Network.ResidualArc

def original {N : Network V A} {f : A → ℝ} (b : N.ResidualArc f) : A := b.val.1

def forward {N : Network V A} {f : A → ℝ} (b : N.ResidualArc f) : Bool := b.val.2

end Network.ResidualArc

namespace ResidualSpec

def graph (N : Network V A) (f : A → ℝ) : Digraph V (N.ResidualArc f) where
  tail b := if b.forward then N.graph.tail b.original else N.graph.head b.original
  head b := if b.forward then N.graph.head b.original else N.graph.tail b.original

noncomputable def step {N : Network V A} {f : A → ℝ}
    (ε : ℝ) (b : N.ResidualArc f) (a : A) : ℝ := by
  classical
  exact if a = b.original then (if b.forward then ε else -ε) else 0

/-- Each occurrence makes its signed modification on its own original arc. -/
noncomputable def adjustment {N : Network V A} {f : A → ℝ}
    (ε : ℝ) (l : List (N.ResidualArc f)) (a : A) : ℝ :=
  (l.map (fun b => step ε b a)).sum

noncomputable def augment (N : Network V A) (f : A → ℝ) {x y : V}
    (p : Walk (graph N f) x y) (ε : ℝ) : A → ℝ :=
  fun a => f a + adjustment ε (Directed.Spec.arcs p) a

/-- ε is attained on the nonempty path and is at most every used capacity. -/
def bottleneck (N : Network V A) (f : A → ℝ) {x y : V}
    (p : Walk (graph N f) x y) (ε : ℝ) : Prop :=
  0 < ε ∧ (∀ b ∈ Directed.Spec.arcs p, ε ≤ capacity N f b.val) ∧
    ∃ b ∈ Directed.Spec.arcs p, ε = capacity N f b.val

section Types
set_option linter.checkUnivs false

def capacityType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Network V A → (A → ℝ) → A × Bool → ℝ

def graphType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (N : Network V A) (f : A → ℝ), Digraph V (N.ResidualArc f)

def augmentType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (N : Network V A) (f : A → ℝ) {x y : V}, Walk (graph N f) x y → ℝ → A → ℝ

end Types

/-- Full original augmentation assertion, including the minimum witness,
original-arc uniqueness and loop exclusion. No restriction is placed on arcs
entering the source, leaving the sink, or on parallel/opposite originals. -/
def augmentation : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), Spec.feasible N f →
    Nonempty (Walk (graph N f) N.source N.sink) →
    ∃ p : Walk (graph N f) N.source N.sink,
      Directed.Spec.isPath p ∧
      ((Directed.Spec.arcs p).map Network.ResidualArc.original).Nodup ∧
      (∀ b ∈ Directed.Spec.arcs p, N.graph.tail b.original ≠ N.graph.head b.original) ∧
      ∃ ε : ℝ, bottleneck N f p ε ∧ Spec.feasible N (augment N f p ε) ∧
        Spec.value N (augment N f p ε) = Spec.value N f + ε

end ResidualSpec
end FiniteCombinatorics.Graph.Flows
