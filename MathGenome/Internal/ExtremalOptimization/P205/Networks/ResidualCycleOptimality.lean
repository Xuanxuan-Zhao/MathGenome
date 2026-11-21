import MathGenome.Internal.ExtremalOptimization.P205.Networks.ResidualFoundation
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualCycleOptimality
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.CirculationDecomposition
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Fintype.BigOperators
import Batteries.Tactic.OpenPrivate

open scoped BigOperators Classical
universe u v
namespace P205.Networks
open FiniteCombinatorics.Directed
open CycleSpec
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- Cost of an elementary signed increment, including an original loop. -/
theorem cost_step (w : A → ℝ) (ε : ℝ) (r : A × Bool) :
    (∑ a, w a * BoundedSpec.step ε r a) = ε * BoundedSpec.cost w r := by
  rw [Finset.sum_eq_single r.1]
  · cases hd : r.2 <;> simp [BoundedSpec.step, BoundedSpec.cost, hd] <;> ring
  · intro a _ ha
    simp [BoundedSpec.step, ha]
  · simp

/-- Linearity gives the precise cost change even for a walk using both signs. -/
theorem cost_adjustment (w : A → ℝ) (ε : ℝ) (l : List (A × Bool)) :
    (∑ a, w a * BoundedSpec.adjustment ε l a) =
      ε * (l.map (BoundedSpec.cost w)).sum := by
  induction l with
  | nil => simp [BoundedSpec.adjustment]
  | cons r l ih =>
    simp only [BoundedSpec.adjustment, List.map_cons, List.sum_cons] at *
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, cost_step, ih]

theorem cost_augment (G : Digraph V A) (lo hi f w : A → ℝ) {x y : V}
    (p : Walk (BoundedSpec.graph G lo hi f) x y) (ε : ℝ) :
    totalCost w (BoundedSpec.augment G lo hi f p ε) =
      totalCost w f + ε * walkCost w lo hi f p := by
  unfold totalCost BoundedSpec.augment
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, cost_adjustment]
  unfold walkCost
  have hm := List.map_map (g := BoundedSpec.cost w)
    (f := fun r : BoundedSpec.ResidualArc lo hi f => r.val) (l := p.arcs)
  exact congrArg (fun l : List ℝ => (∑ a, w a * f a) + ε * l.sum) hm

theorem negative_cycle_improves : CycleSpec.negative_cycle_improves.{u,v} := by
  intro V A _ _ G lo hi b w f hf x p hp hc
  obtain ⟨ε, hε⟩ := cycle_bottleneck G lo hi f p hp
  refine ⟨ε, hε.1, hε, augment_cycle G lo hi f b p hp hf ε ε hε hε.1.le le_rfl, ?_⟩
  rw [cost_augment]
  have := mul_neg_of_pos_of_neg hε.1 hc
  linarith

omit [Fintype A] in
/-- Raw comparison loads vanish on signed copies absent from the residual graph. -/
private theorem comparison_zero (lo hi f h : A → ℝ)
    (hh : BoundedSpec.WithinBounds lo hi h)
    (r : A × Bool) (hr : ¬ 0 < BoundedSpec.capacity lo hi f r) :
    (if r.2 then max (h r.1 - f r.1) 0 else max (f r.1 - h r.1) 0) = 0 := by
  have hcap := le_of_not_gt hr
  cases hd : r.2
  · simp only [BoundedSpec.capacity, hd, Bool.false_eq_true, ↓reduceIte] at hcap
    change max (f r.1 - h r.1) 0 = 0
    exact max_eq_right (by linarith [(hh r.1).1])
  · simp only [BoundedSpec.capacity, hd, ↓reduceIte] at hcap
    change max (h r.1 - f r.1) 0 = 0
    exact max_eq_right (by linarith [(hh r.1).2])

/-- Extend a residual sum by zero to all original signed labels. -/
private theorem comparison_sum (lo hi f h : A → ℝ)
    (_hf : BoundedSpec.WithinBounds lo hi f) (hh : BoundedSpec.WithinBounds lo hi h)
    (k : A × Bool → ℝ) :
    (∑ r : BoundedSpec.ResidualArc lo hi f, k r.val * comparisonLoad lo hi f h r) =
    ∑ r : A × Bool, k r *
      (if r.2 then max (h r.1 - f r.1) 0 else max (f r.1 - h r.1) 0) := by
  classical
  change (∑ r : {r : A × Bool // 0 < BoundedSpec.capacity lo hi f r},
    k r.val * (if r.val.2 then max (h r.val.1 - f r.val.1) 0
      else max (f r.val.1 - h r.val.1) 0)) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun r => 0 < BoundedSpec.capacity lo hi f r))
    (by simp) (fun r : A × Bool => k r *
      (if r.2 then max (h r.1 - f r.1) 0 else max (f r.1 - h r.1) 0))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : 0 < BoundedSpec.capacity lo hi f r
  · simp [hr]
  · simp [hr, comparison_zero lo hi f h hh r hr]

/-- The residual cost of a comparison equals the original linear cost difference. -/
theorem comparison_weighted (lo hi f h w : A → ℝ)
    (hf : BoundedSpec.WithinBounds lo hi f) (hh : BoundedSpec.WithinBounds lo hi h) :
    (∑ r : BoundedSpec.ResidualArc lo hi f,
      BoundedSpec.cost w r.val * comparisonLoad lo hi f h r) =
      ∑ a, w a * (h a - f a) := by
  rw [comparison_sum lo hi f h hf hh (BoundedSpec.cost w), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_bool]
  simp only [BoundedSpec.cost, Bool.false_eq_true, ↓reduceIte]
  by_cases ha : f a ≤ h a
  · rw [max_eq_left (sub_nonneg.mpr ha), max_eq_right (sub_nonpos.mpr ha)]
    ring
  · have ha' := le_of_not_ge ha
    rw [max_eq_right (sub_nonpos.mpr ha'), max_eq_left (sub_nonneg.mpr ha')]
    ring

/-- Write divergence as a linear functional with its net-outflow incidence row. -/
theorem divergence_eq_incidence_sum (G : Digraph V A) (f : A → ℝ) (x : V) :
    G.divergence f x = ∑ a,
      ((if G.tail a = x then (1 : ℝ) else 0) -
       (if G.head a = x then (1 : ℝ) else 0)) * f a := by
  rw [Digraph.divergence_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

private theorem residual_incidence (G : Digraph V A) (lo hi f : A → ℝ) (x : V)
    (r : BoundedSpec.ResidualArc lo hi f) :
    ((if (BoundedSpec.graph G lo hi f).tail r = x then (1 : ℝ) else 0) -
     (if (BoundedSpec.graph G lo hi f).head r = x then (1 : ℝ) else 0)) =
    BoundedSpec.cost (fun a => (if G.tail a = x then 1 else 0) -
      (if G.head a = x then 1 else 0)) r.val := by
  cases hd : r.val.2
  · simp only [BoundedSpec.graph, BoundedSpec.cost, hd, Bool.false_eq_true, ↓reduceIte]
    ring
  · simp only [BoundedSpec.graph, BoundedSpec.cost, hd, ↓reduceIte]

theorem comparison_divergence (G : Digraph V A) (lo hi f h : A → ℝ)
    (hf : BoundedSpec.WithinBounds lo hi f) (hh : BoundedSpec.WithinBounds lo hi h)
    (x : V) :
    (BoundedSpec.graph G lo hi f).divergence (comparisonLoad lo hi f h) x =
      G.divergence h x - G.divergence f x := by
  rw [divergence_eq_incidence_sum]
  simp_rw [residual_incidence]
  rw [comparison_weighted lo hi f h _ hf hh, divergence_eq_incidence_sum G h,
    divergence_eq_incidence_sum G f, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem comparison_properties : CycleSpec.comparison_properties.{u,v} := by
  intro V A _ _ G lo hi b w f h hf hh
  refine ⟨?_, ?_, ?_⟩
  · intro r
    unfold comparisonLoad
    split_ifs <;> exact le_max_right _ _
  · intro x
    rw [comparison_divergence G lo hi f h hf.1 hh.1, hf.2, hh.2, sub_self]
  · rw [comparison_weighted lo hi f h w hf.1 hh.1]
    simp only [totalCost, mul_sub, Finset.sum_sub_distrib]

open private sum_mem_list from
  MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.CirculationDecomposition

/-- The linear cost of one weighted cycle is its coefficient times its arc cost. -/
theorem cost_cycle_contribution (G : Digraph V A) (w : A → ℝ)
    (ε : ℝ) (c : Spec.cycle G) :
    (∑ a, w a * CirculationSpec.contribution ε c a) =
      ε * (c.2.val.arcs.map w).sum := by
  calc
    _ = ∑ a : A, if a ∈ c.2.val.arcs then ε * w a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      unfold CirculationSpec.contribution
      change w a * (if a ∈ c.2.val.arcs then ε else 0) = _
      split_ifs <;> ring
    _ = (c.2.val.arcs.map (fun a => ε * w a)).sum :=
      sum_mem_list _ (Circulation.cycle_arcs_nodup c) _
    _ = _ := List.sum_map_mul_left _ _ _

/-- A finite decomposition is compatible with every linear cost functional. -/
theorem cost_decomposition (G : Digraph V A) (w q : A → ℝ)
    (d : List (ℝ × Spec.cycle G))
    (hd : ∀ a, q a = (d.map fun t => CirculationSpec.contribution t.1 t.2 a).sum) :
    (∑ a, w a * q a) =
      (d.map fun t => t.1 * (t.2.2.val.arcs.map w).sum).sum := by
  simp_rw [hd]
  clear hd q
  induction d with
  | nil => simp
  | cons t d ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    rw [cost_cycle_contribution, ih]

/-- A nonnegative circulation has nonnegative cost when all simple cycles do. -/
theorem circulation_cost_nonneg (G : Digraph V A) (w q : A → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hb : ∀ x, G.divergence q x = 0)
    (hc : ∀ c : Spec.cycle G, 0 ≤ (c.2.val.arcs.map w).sum) :
    0 ≤ ∑ a, w a * q a := by
  obtain ⟨d, hd⟩ := circulation_decomposition G q hq hb
  rw [cost_decomposition G w q d hd.2]
  apply List.sum_nonneg
  intro z hz
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
  exact mul_nonneg (hd.1 t ht).le (hc t.2)

/-- W39 (items 1 and 2), for arbitrary finite real bounds and prescribed divergence. -/
theorem residual_cycle_optimality : CycleSpec.residual_cycle_optimality.{u,v} := by
  intro V A _ _ G lo hi b w f hf
  constructor
  · intro ho x p hp
    by_contra hn
    obtain ⟨ε, _, _, hh, hc⟩ :=
      negative_cycle_improves G lo hi b w f hf x p hp (lt_of_not_ge hn)
    exact (not_lt_of_ge (ho _ hh)) hc
  · intro hn h hh
    obtain ⟨hpos, hbal, hcost⟩ := comparison_properties G lo hi b w f h hf hh
    have hnonneg := circulation_cost_nonneg (BoundedSpec.graph G lo hi f)
      (fun r => BoundedSpec.cost w r.val) (comparisonLoad lo hi f h) hpos hbal
      (fun c => hn c.1 c.2.val c.2.property)
    rw [hcost] at hnonneg
    exact sub_nonneg.mp hnonneg

end P205.Networks
