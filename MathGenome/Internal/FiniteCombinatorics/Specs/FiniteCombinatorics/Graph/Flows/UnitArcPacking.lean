import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations
import Mathlib.Data.Finset.Card

/-! Unit-arc extraction used in W48, from the original-arc decomposition of W47. -/
universe u v
namespace FiniteCombinatorics.Graph.Flows.UnitArcPackingSpec
open FiniteCombinatorics.Directed

/-- Integral feasible loads yield an actual finite family of simple paths,
with no selected unit arc shared by two paths. The zero case uses the empty family. -/
def unit_arc_packing : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (B : Finset A),
    (∀ a ∈ B, N.capacity a = 1) →
    (∀ p : Directed.Spec.path N.graph N.source N.sink,
      ∃ a ∈ B, a ∈ Directed.Spec.arcs p.val) →
    ∀ f : A → ℝ, Spec.feasible N f →
    (∀ a, ∃ z : ℤ, (z : ℝ) = f a) → 0 ≤ Spec.value N f →
    ∃ D : Finset (Directed.Spec.path N.graph N.source N.sink),
      (D.card : ℝ) = Spec.value N f ∧
      (∀ p ∈ D, ∀ q ∈ D, p ≠ q → ∀ a ∈ B,
        ¬ (a ∈ Directed.Spec.arcs p.val ∧ a ∈ Directed.Spec.arcs q.val)) ∧
      (Spec.value N f = 0 → D = ∅)

end FiniteCombinatorics.Graph.Flows.UnitArcPackingSpec
