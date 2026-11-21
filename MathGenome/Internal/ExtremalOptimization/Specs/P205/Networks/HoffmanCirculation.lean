import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.HoffmanReduction

/-! Independent statements of paper.tex, W38 (1776–1816).
The shared labelled digraph, real bounds, net-outflow divergence and cut sums
retain loops, parallel/opposite arcs and empty finite types. No nonnegativity
of the lower bounds or initial feasible flow is assumed. -/

open scoped BigOperators Classical
universe u v
namespace P205.Networks.HoffmanCirculationSpec
open FiniteCombinatorics.Directed
open HoffmanSpec

/-- The full bounded fixed-divergence feasibility criterion, for every cut. -/
def hoffman_fixed_divergence : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ),
    (∀ a, lo a ≤ hi a) → (∑ x, b x) = 0 →
    ((∃ f : A → ℝ, BoundedSpec.Feasible G lo hi b f) ↔ CutCondition G lo hi b)

/-- For integer-valued data, the same cut criterion gives an integral witness. -/
def integral_hoffman_fixed_divergence : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ),
    (∀ a, lo a ≤ hi a) → (∑ x, b x) = 0 →
    Integral lo → Integral hi → Integral b →
    ((∃ f : A → ℝ, BoundedSpec.Feasible G lo hi b f ∧ Integral f) ↔
      CutCondition G lo hi b)

/-- Zero divergence specializes to the circulation criterion. -/
def hoffman_circulation : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ), (∀ a, lo a ≤ hi a) →
    ((∃ f : A → ℝ, BoundedSpec.Feasible G lo hi (fun _ => 0) f) ↔
      ∀ S : Set V, BoundedSpec.arcSum lo (BoundedSpec.incoming G S) ≤
        BoundedSpec.arcSum hi (BoundedSpec.outgoing G S))

/-- Integral bounds give an integral circulation under the same criterion. -/
def integral_hoffman_circulation : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ), (∀ a, lo a ≤ hi a) →
    Integral lo → Integral hi →
    ((∃ f : A → ℝ, BoundedSpec.Feasible G lo hi (fun _ => 0) f ∧ Integral f) ↔
      ∀ S : Set V, BoundedSpec.arcSum lo (BoundedSpec.incoming G S) ≤
        BoundedSpec.arcSum hi (BoundedSpec.outgoing G S))

end P205.Networks.HoffmanCirculationSpec
