import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualFoundation

/-! Cost optimality in a finite bounded fixed-divergence problem (W39, items 1–2).
All arc labels, both residual signs, arbitrary real bounds, and loops are retained. -/
open scoped BigOperators Classical
universe u v
namespace P205.Networks.CycleSpec
open FiniteCombinatorics.Directed
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

noncomputable def totalCost (w f : A → ℝ) : ℝ := ∑ a, w a * f a
noncomputable def walkCost (w : A → ℝ) {G : Digraph V A} (lo hi f : A → ℝ)
    {x y : V} (p : Walk (BoundedSpec.graph G lo hi f) x y) : ℝ :=
  (p.arcs.map (fun r => BoundedSpec.cost w r.val)).sum

def NoNegativeCycles (G : Digraph V A) (lo hi f w : A → ℝ) : Prop :=
  ∀ (x : V) (p : Walk (BoundedSpec.graph G lo hi f) x x),
    p.IsCycle → 0 ≤ walkCost w lo hi f p

def Optimal (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ)
    (w f : A → ℝ) : Prop :=
  ∀ h : A → ℝ, BoundedSpec.Feasible G lo hi b h → totalCost w f ≤ totalCost w h

/-- Positive/negative parts of the comparison, on the positive residual copies. -/
noncomputable def comparisonLoad (lo hi f h : A → ℝ)
    (r : BoundedSpec.ResidualArc lo hi f) : ℝ :=
  if r.val.2 then max (h r.val.1 - f r.val.1) 0
  else max (f r.val.1 - h r.val.1) 0

set_option linter.checkUnivs false in
def comparison_properties : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) (w f h : A → ℝ),
    BoundedSpec.Feasible G lo hi b f → BoundedSpec.Feasible G lo hi b h →
    (∀ r, 0 ≤ comparisonLoad lo hi f h r) ∧
    (∀ x, (BoundedSpec.graph G lo hi f).divergence (comparisonLoad lo hi f h) x = 0) ∧
    (∑ r, BoundedSpec.cost w r.val * comparisonLoad lo hi f h r) =
      totalCost w h - totalCost w f

set_option linter.checkUnivs false in
def negative_cycle_improves : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) (w f : A → ℝ),
    BoundedSpec.Feasible G lo hi b f →
    ∀ (x : V) (p : Walk (BoundedSpec.graph G lo hi f) x x), p.IsCycle →
      walkCost w lo hi f p < 0 →
      ∃ ε : ℝ, 0 < ε ∧ BoundedSpec.Bottleneck G lo hi f p ε ∧
        BoundedSpec.Feasible G lo hi b (BoundedSpec.augment G lo hi f p ε) ∧
        totalCost w (BoundedSpec.augment G lo hi f p ε) < totalCost w f

set_option linter.checkUnivs false in
def residual_cycle_optimality : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) (w f : A → ℝ),
    BoundedSpec.Feasible G lo hi b f →
    (Optimal G lo hi b w f ↔ NoNegativeCycles G lo hi f w)
end P205.Networks.CycleSpec
