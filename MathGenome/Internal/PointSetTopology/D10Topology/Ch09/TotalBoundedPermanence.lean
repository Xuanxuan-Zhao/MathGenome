import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.TotalBoundedPermanence
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions

/-! Permanence and consequences of total boundedness
(paper.tex, d10:09:total-bounded-basics).
The subset bridge uses the uniform inducing inclusion, whose finite-cover
proof recenters covers inside the subset. Thus all subsequent subset results
retain the paper's requirement on centers, including for empty subsets.
-/

open Set
universe u v

namespace D10Topology.Ch09

theorem totallyBounded_subspace_iff {X : Type u} [d : MetricSpace X] (A : Set X) :
    TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace ↔
      _root_.TotallyBounded A := by
  rw [totallyBounded_iff_mathlib]
  simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using
    (totallyBounded_image_iff
      (isUniformEmbedding_subtype_val (p := fun x : X => x ∈ A)).isUniformInducing
      (s := (univ : Set A))).symm

theorem totallyBounded_subspace {X : Type u} [d : MetricSpace X] (A : Set X)
    (h : TotallyBounded d.toPseudoMetricSpace) :
    TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace := by
  exact (totallyBounded_subspace_iff A).mpr
    (((totallyBounded_iff_mathlib d.toPseudoMetricSpace).mp h).subset (subset_univ A))

theorem totallyBounded_closure {X : Type u} [d : MetricSpace X] (A : Set X)
    (h : TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace) :
    TotallyBounded (inferInstance : MetricSpace (closure A)).toPseudoMetricSpace := by
  exact (totallyBounded_subspace_iff (closure A)).mpr
    (((totallyBounded_subspace_iff A).mp h).closure)

theorem totallyBounded_image {X : Type u} {Y : Type v}
    [d : MetricSpace X] [e : MetricSpace Y] (f : X → Y) (A : Set X)
    (hf : UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace f)
    (h : TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace) :
    TotallyBounded (inferInstance : MetricSpace (f '' A)).toPseudoMetricSpace := by
  exact (totallyBounded_subspace_iff (f '' A)).mpr
    (((totallyBounded_subspace_iff A).mp h).image
      ((uniformlyContinuous_iff_mathlib d.toPseudoMetricSpace e.toPseudoMetricSpace f).mp hf))

theorem totallyBounded_bounded {X : Type u} [d : MetricSpace X]
    (h : TotallyBounded d.toPseudoMetricSpace) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x y : X, distance d.toPseudoMetricSpace x y ≤ R := by
  obtain ⟨R, hR, hb⟩ := (Metric.isBounded_iff_exists_ge 0).mp
    (((totallyBounded_iff_mathlib d.toPseudoMetricSpace).mp h).isBounded)
  exact ⟨R, hR, fun x y => hb (mem_univ x) (mem_univ y)⟩

theorem totallyBounded_separable {X : Type u} [d : MetricSpace X]
    (h : TotallyBounded d.toPseudoMetricSpace) :
    Ch08.Separable (metricTopology d.toPseudoMetricSpace) := by
  exact TopologicalSpace.isSeparable_univ_iff.mp
    (((totallyBounded_iff_mathlib d.toPseudoMetricSpace).mp h).isSeparable)

theorem totallyBounded_countable_dense {X : Type u} [d : MetricSpace X]
    (h : TotallyBounded d.toPseudoMetricSpace) :
    ∃ D : Set X, D.Countable ∧ closure D = univ := by
  exact Ch08.separable_iff_countable_dense.mp (totallyBounded_separable h)

theorem unit_discrete_metric_exists (X : Type u) :
    ∃ d : MetricSpace X,
      ∀ x y : X, x ≠ y → distance d.toPseudoMetricSpace x y = 1 := by
  classical
  let d : MetricSpace X :=
    { dist x y := if x = y then 0 else 1
      dist_self x := by simp
      dist_comm x y := by
        by_cases h : x = y
        · simp [h]
        · simp [h, Ne.symm h]
      dist_triangle x y z := by
        by_cases x = y <;> by_cases x = z <;> by_cases y = z <;> simp_all
      eq_of_dist_eq_zero := by simp }
  exact ⟨d, fun x y h => ite_eq_right h⟩

theorem infinite_unit_discrete_not_totallyBounded {X : Type u} [Infinite X]
    [d : MetricSpace X]
    (hd : ∀ x y : X, x ≠ y → distance d.toPseudoMetricSpace x y = 1) :
    (∀ x y : X, distance d.toPseudoMetricSpace x y ≤ 1) ∧
      ¬ TotallyBounded d.toPseudoMetricSpace := by
  constructor
  · intro x y
    by_cases h : x = y
    · subst y
      exact (dist_self x).le.trans zero_le_one
    · exact (hd x y h).le
  · intro h
    obtain ⟨F, hF, hcover⟩ := h (1 / 2) (by norm_num)
    have huniv : (univ : Set X) ⊆ F := by
      intro x hx
      have hxcover : x ∈ ⋃ c ∈ F, ball d.toPseudoMetricSpace c (1 / 2) :=
        hcover.symm ▸ hx
      obtain ⟨c, hc, hcx⟩ := mem_iUnion₂.mp hxcover
      have hxc : c = x := by
        by_contra hn
        change distance d.toPseudoMetricSpace c x < 1 / 2 at hcx
        rw [hd c x hn] at hcx
        norm_num at hcx
      exact hxc ▸ hc
    exact Set.infinite_univ (hF.subset huniv)

theorem infinite_unit_discrete_counterexample (X : Type u) [Infinite X] :
    ∃ d : MetricSpace X,
      (∀ x y : X, x ≠ y → distance d.toPseudoMetricSpace x y = 1) ∧
      (∀ x y : X, distance d.toPseudoMetricSpace x y ≤ 1) ∧
        ¬ TotallyBounded d.toPseudoMetricSpace := by
  obtain ⟨d, hd⟩ := unit_discrete_metric_exists X
  let := d
  exact ⟨d, hd, infinite_unit_discrete_not_totallyBounded hd⟩

end D10Topology.Ch09
