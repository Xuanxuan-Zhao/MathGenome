import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.MetricSeparation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Tactic.Linarith

/-! Metric separation, paper.tex, d10:07:metric-normal. -/

open Set
universe u

namespace D10Topology.Ch07

theorem metric_infDist_eq_infimum {X : Type u} (d : MetricSpace X)
    (A : Set X) (x : X) :
    letI := d
    Metric.infDist x A = sInf ((fun a => dist x a) '' A) := by
  letI := d
  rw [Metric.infDist_eq_iInf, sInf_image']

theorem metric_infDist_lipschitz {X : Type u} (d : MetricSpace X)
    (A : Set X) (_hA : A.Nonempty) :
    letI := d
    LipschitzWith 1 (fun x => Metric.infDist x A) := by
  letI := d
  exact Metric.lipschitz_infDist_pt A

theorem metric_infDist_estimate {X : Type u} (d : MetricSpace X)
    (A : Set X) (hA : A.Nonempty) :
    letI := d
    ∀ x y : X, |Metric.infDist x A - Metric.infDist y A| ≤ dist x y := by
  letI := d
  intro x y
  simpa only [Real.dist_eq, one_mul, NNReal.coe_one] using
    (metric_infDist_lipschitz d A hA).dist_le_mul x y

theorem metric_infDist_zero_set {X : Type u} (d : MetricSpace X)
    (A : Set X) (hA : A.Nonempty) :
    letI := d
    {x : X | Metric.infDist x A = 0} = closure A := by
  letI := d
  ext x
  exact (Metric.mem_closure_iff_infDist_zero hA).symm

theorem metric_distance_denominator_pos {X : Type u} (d : MetricSpace X)
    (A B : Set X) :
    letI := d
    IsClosed A → IsClosed B → A.Nonempty → B.Nonempty → Disjoint A B →
    ∀ x : X, 0 < Metric.infDist x A + Metric.infDist x B := by
  letI := d
  intro hAc hBc hA hB hAB x
  by_cases hx : x ∈ A
  · have hxB : x ∉ B := fun hy => Set.disjoint_left.mp hAB hx hy
    exact add_pos_of_nonneg_of_pos Metric.infDist_nonneg
      ((hBc.notMem_iff_infDist_pos hB).mp hxB)
  · exact add_pos_of_pos_of_nonneg ((hAc.notMem_iff_infDist_pos hA).mp hx)
      Metric.infDist_nonneg

theorem metric_distance_quotient {X : Type u} (d : MetricSpace X)
    (A B : Set X) :
    letI := d
    IsClosed A → IsClosed B → A.Nonempty → B.Nonempty → Disjoint A B →
    let f : X → ℝ := fun x =>
      Metric.infDist x A / (Metric.infDist x A + Metric.infDist x B)
    Continuous f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ A, f x = 0) ∧ (∀ x ∈ B, f x = 1) := by
  letI := d
  intro hAc hBc hA hB hAB
  have hpos := metric_distance_denominator_pos d A B hAc hBc hA hB hAB
  refine ⟨(Metric.continuous_infDist_pt A).div
      ((Metric.continuous_infDist_pt A).add (Metric.continuous_infDist_pt B))
      (fun x => ne_of_gt (hpos x)), ?_, ?_, ?_⟩
  · intro x
    exact ⟨div_nonneg Metric.infDist_nonneg (hpos x).le,
      (div_le_one (hpos x)).mpr (le_add_of_nonneg_right Metric.infDist_nonneg)⟩
  · intro x hx
    simp only [Metric.infDist_zero_of_mem hx, zero_div]
  · intro x hx
    have hne : Metric.infDist x A ≠ 0 := by
      have := hpos x
      rw [Metric.infDist_zero_of_mem hx, add_zero] at this
      exact ne_of_gt this
    simp only [Metric.infDist_zero_of_mem hx, add_zero, div_self hne]

theorem metric_closed_separation {X : Type u} (d : MetricSpace X)
    (A B : Set X) :
    letI := d
    IsClosed A → IsClosed B → Disjoint A B →
    ∃ f : X → ℝ, Continuous f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ A, f x = 0) ∧ (∀ x ∈ B, f x = 1) := by
  letI := d
  intro hAc hBc hAB
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨fun _ => 1, continuous_const, fun _ => ⟨zero_le_one, le_rfl⟩,
      fun _ hx => False.elim hx, fun _ _ => rfl⟩
  rcases B.eq_empty_or_nonempty with rfl | hB
  · exact ⟨fun _ => 0, continuous_const, fun _ => ⟨le_rfl, zero_le_one⟩,
      fun _ _ => rfl, fun _ hx => False.elim hx⟩
  exact ⟨_, metric_distance_quotient d A B hAc hBc hA hB hAB⟩

theorem metric_t4 {X : Type u} (d : MetricSpace X) :
    letI := d
    T4 X := by
  letI := d
  refine ⟨(normal_iff_disjoint_open X).mpr ?_, inferInstance⟩
  intro A B hAc hBc hAB
  obtain ⟨f, hf, _, hfA, hfB⟩ := metric_closed_separation d A B hAc hBc hAB
  refine ⟨{x | f x < 1 / 3}, {x | 2 / 3 < f x},
    isOpen_lt hf continuous_const, isOpen_lt continuous_const hf, ?_, ?_, ?_⟩
  · intro x hx
    change f x < 1 / 3
    rw [hfA x hx]
    norm_num
  · intro x hx
    change 2 / 3 < f x
    rw [hfB x hx]
    norm_num
  · exact Set.disjoint_left.mpr (fun x hx hy => by
      change f x < 1 / 3 at hx
      change 2 / 3 < f x at hy
      linarith)

theorem metric_closed_gdelta {X : Type u} (d : MetricSpace X) :
    letI := d
    ∀ A : Set X, IsClosed A → GDelta A := by
  letI := d
  intro A hA
  exact hA.isGδ

end D10Topology.Ch07
