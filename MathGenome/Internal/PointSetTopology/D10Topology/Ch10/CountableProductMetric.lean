import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.CountableProductMetric
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Tactic.Positivity

/-! The precise weighted sum in d10:10:product-metric. We rescale coordinate
metrics before applying `PiCountable.metricSpace`, and rescale the resulting
metric by 1/2. All these constructions retain the product uniformity, which
also proves completeness without imposing nonemptiness on any factor. -/

open Filter
open scoped Topology
universe u
namespace D10Topology.Ch10
open D10Topology.Ch09

noncomputable def productDistance {X : ℕ → Type u} (d : ∀ n, MetricSpace (X n))
    (x y : ∀ n, X n) : ℝ :=
  ∑' n : ℕ, (2⁻¹ : ℝ) ^ (n + 1) * min 1 (distance (d n).toPseudoMetricSpace (x n) (y n))

/-- Multiplying a metric by a positive constant retains its uniformity. -/
@[instance_reducible] noncomputable def rescaledMetric {Y : Type u} (d : MetricSpace Y) (c : ℝ) (hc : 0 < c) :
    MetricSpace Y := by
  letI := d
  exact {
    dist := fun x y => c * dist x y
    dist_self := fun x => by simp
    dist_comm := fun x y => by rw [dist_comm]
    dist_triangle := fun x y z => by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (dist_triangle x y z) hc.le
    eq_of_dist_eq_zero := fun h => eq_of_dist_eq_zero ((mul_eq_zero.mp h).resolve_left hc.ne')
    toUniformSpace := d.toUniformSpace
    uniformity_dist := by
      apply Filter.HasBasis.eq_biInf
      apply Metric.uniformity_basis_dist.to_hasBasis
      · intro ε hε
        refine ⟨c * ε, mul_pos hc hε, ?_⟩
        intro p hp
        exact (mul_lt_mul_iff_right₀ hc).mp hp
      · intro ε hε
        refine ⟨ε / c, div_pos hε hc, ?_⟩
        intro p hp
        change c * dist p.1 p.2 < ε
        simpa only [mul_comm] using (lt_div_iff₀ hc).mp hp }

private theorem rescaled_dist {Y : Type u} (d : MetricSpace Y) (c : ℝ) (hc : 0 < c)
    (x y : Y) :
    @dist Y (rescaledMetric d c hc).toDist x y = c * @dist Y d.toDist x y := rfl

/-- The witness metric. The equality of uniformities is built into the
construction, rather than recovered just from equality of topologies. -/
@[instance_reducible] noncomputable def productMetric {X : ℕ → Type u}
    (d : ∀ n, MetricSpace (X n)) : MetricSpace (∀ n, X n) :=
  letI : ∀ n, MetricSpace (X n) :=
    fun n => rescaledMetric (d n) ((2⁻¹ : ℝ) ^ n) (by positivity)
  rescaledMetric PiCountable.metricSpace (2⁻¹ : ℝ) (by positivity)

theorem productMetric_dist {X : ℕ → Type u} (d : ∀ n, MetricSpace (X n))
    (x y : ∀ n, X n) :
    distance (productMetric d).toPseudoMetricSpace x y = productDistance d x y := by
  change (2⁻¹ : ℝ) * (∑' n : ℕ,
      min ((2⁻¹ : ℝ) ^ Encodable.encode n)
        (((2⁻¹ : ℝ) ^ n) * distance (d n).toPseudoMetricSpace (x n) (y n))) = _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  change (2⁻¹ : ℝ) * min ((2⁻¹ : ℝ) ^ n)
    (((2⁻¹ : ℝ) ^ n) * distance (d n).toPseudoMetricSpace (x n) (y n)) = _
  rw [show min ((2⁻¹ : ℝ) ^ n) (((2⁻¹ : ℝ) ^ n) *
      distance (d n).toPseudoMetricSpace (x n) (y n)) =
      ((2⁻¹ : ℝ) ^ n) * min 1 (distance (d n).toPseudoMetricSpace (x n) (y n)) by
    simpa only [mul_one] using
      (mul_min_of_nonneg (1 : ℝ) (distance (d n).toPseudoMetricSpace (x n) (y n))
        (show 0 ≤ (2⁻¹ : ℝ) ^ n by positivity)).symm]
  simp only [pow_succ, mul_assoc, mul_comm]

theorem product_series_summable {X : ℕ → Type u} (d : ∀ n, MetricSpace (X n))
    (x y : ∀ n, X n) :
    Summable (fun n : ℕ => (2⁻¹ : ℝ) ^ (n + 1) *
      min 1 (distance (d n).toPseudoMetricSpace (x n) (y n))) := by
  let : ∀ n, MetricSpace (X n) := d
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (r := (2⁻¹ : ℝ)) (by positivity) (by norm_num)))
  · dsimp only [distance]
    positivity
  · exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)

theorem productMetric_topology {X : ℕ → Type u} (d : ∀ n, MetricSpace (X n)) :
    metricTopology (productMetric d).toPseudoMetricSpace =
      D10Topology.Ch03.productTopology (fun n => metricTopology (d n).toPseudoMetricSpace) := by
  rw [D10Topology.Ch03.productTopology_eq_pi]
  rfl

theorem productMetric_complete {X : ℕ → Type u} (d : ∀ n, MetricSpace (X n))
    (hd : ∀ n, SequentiallyComplete (d n).toPseudoMetricSpace) :
    SequentiallyComplete (productMetric d).toPseudoMetricSpace := by
  let : ∀ n, MetricSpace (X n) := d
  let : ∀ n, CompleteSpace (X n) :=
    fun n => (sequentiallyComplete_iff_mathlib _).mp (hd n)
  apply (sequentiallyComplete_iff_mathlib _).mpr
  change @CompleteSpace (∀ n, X n) (@Pi.uniformSpace ℕ X (fun n => (d n).toUniformSpace))
  infer_instance

theorem product_metric_exists {X : ℕ → Type u} (d : ∀ n, MetricSpace (X n)) :
    ∃ m : MetricSpace (∀ n, X n),
      distance m.toPseudoMetricSpace = productDistance d ∧
      metricTopology m.toPseudoMetricSpace =
        D10Topology.Ch03.productTopology (fun n => metricTopology (d n).toPseudoMetricSpace) ∧
      ((∀ n, SequentiallyComplete (d n).toPseudoMetricSpace) →
        SequentiallyComplete m.toPseudoMetricSpace) := by
  exact ⟨productMetric d, funext fun x => funext fun y => productMetric_dist d x y,
    productMetric_topology d, productMetric_complete d⟩

end D10Topology.Ch10
