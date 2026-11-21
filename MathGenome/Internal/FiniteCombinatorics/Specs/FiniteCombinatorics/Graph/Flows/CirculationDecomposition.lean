import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Directed.Foundations
import Mathlib.Algebra.Order.Ring.Int

/-! Independent statements for the circulation assertions of W47.
Cycles use the shared original-arc interface, including one-arc loops.
A list is a finite indexed family; repeated cycles are allowed. -/

open scoped BigOperators
universe u v
namespace FiniteCombinatorics.Directed.CirculationSpec
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- A weighted simple cycle contributes its weight to every original arc it uses. -/
noncomputable def contribution {R : Type*} [Zero R] {G : Digraph V A}
    (w : R) (c : Spec.cycle G) (a : A) : R := by
  classical
  exact if a ∈ Spec.arcs c.2.val then w else 0

/-- Positivity and equality on every original indexed arc. -/
def Decomposes {R : Type*} [AddCommMonoid R] [LT R] {G : Digraph V A}
    (f : A → R) (d : List (R × Spec.cycle G)) : Prop :=
  (∀ t ∈ d, 0 < t.1) ∧
  ∀ a, f a = (d.map fun t => contribution t.1 t.2 a).sum

def real_decomposition : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (f : A → ℝ),
    (∀ a, 0 ≤ f a) → (∀ x, Spec.divergence G f x = 0) →
    ∃ d : List (ℝ × Spec.cycle G), Decomposes f d

def integer_decomposition : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (f : A → ℝ),
    (∀ a, 0 ≤ f a) → (∀ x, Spec.divergence G f x = 0) →
    (∀ a, ∃ z : ℤ, (z : ℝ) = f a) →
    ∃ d : List (ℤ × Spec.cycle G),
      (∀ t ∈ d, 0 < t.1) ∧
      ∀ a, f a = ((d.map fun t => contribution t.1 t.2 a).sum : ℤ)

def zero_decomposition : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A] (G : Digraph V A),
    Decomposes (G := G) (fun _ => (0 : ℝ)) []
end FiniteCombinatorics.Directed.CirculationSpec
