import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakMetrics
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.BorelRegularity
import Mathlib.MeasureTheory.Measure.Portmanteau
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.BoundedLipschitzMetric
import Mathlib.Topology.Sequences

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped NNReal

namespace ProbabilityFoundations.Ch06

universe u v
noncomputable section
variable {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

theorem boundedLipschitzDist_self (μ : ProbabilityMeasure S) :
    boundedLipschitzDist μ μ = 0 := by
  apply le_antisymm _ (boundedLipschitzDist_bounds μ μ).1
  apply csSup_le (boundedLipschitzValues_nonempty μ μ)
  rintro r ⟨f, hf, rfl⟩
  simp

theorem boundedLipschitzDist_comm (μ ν : ProbabilityMeasure S) :
    boundedLipschitzDist μ ν = boundedLipschitzDist ν μ := by
  unfold boundedLipschitzDist
  congr 1
  ext r
  simp only [abs_sub_comm]

theorem boundedLipschitzDist_triangle (μ ν ξ : ProbabilityMeasure S) :
    boundedLipschitzDist μ ξ ≤ boundedLipschitzDist μ ν + boundedLipschitzDist ν ξ := by
  apply csSup_le (boundedLipschitzValues_nonempty μ ξ)
  rintro r ⟨f, hf, rfl⟩
  exact (abs_sub_le _ _ _).trans (add_le_add
    (test_integral_le_boundedLipschitzDist μ ν f hf)
    (test_integral_le_boundedLipschitzDist ν ξ f hf))

/-- Scaling an arbitrary bounded Lipschitz function into the two unit bounds. -/
lemma integral_sub_le_boundedLipschitzDist (μ ν : ProbabilityMeasure S)
    (f : S →ᵇ ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) :
    |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)| ≤
      (‖f‖ + L + 1) * boundedLipschitzDist μ ν := by
  let C : ℝ := ‖f‖ + L + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let g : S → ℝ := fun x => (C⁻¹) * f x
  have hg : IsBoundedLipschitzTest g := by
    constructor
    · intro x
      dsimp [g]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hC)]
      apply (inv_mul_le_one₀ hC).mpr
      exact (show |f x| ≤ ‖f‖ from f.norm_coe_le_norm x).trans (by dsimp [C]; linarith [L.coe_nonneg])
    · apply (lipschitzWith_iff_dist_le_mul).mpr
      intro x y
      simp only [g, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hC)]
      calc
        C⁻¹ * |f x - f y| ≤ C⁻¹ * ((L : ℝ) * dist x y) :=
          mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using hf.dist_le_mul x y)
            (inv_nonneg.mpr hC.le)
        _ ≤ 1 * dist x y := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            ((inv_mul_le_one₀ hC).mpr (by dsimp [C]; linarith [norm_nonneg f])) dist_nonneg
  have h := test_integral_le_boundedLipschitzDist μ ν g hg
  simp only [g, integral_const_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hC)] at h
  have hm := mul_le_mul_of_nonneg_left h hC.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using hm

/-- The sequence criterion is used only to establish continuity of the metric-domain map. -/
lemma weaklyConverges_of_boundedLipschitzDist_sequence
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (h : Tendsto (fun n => boundedLipschitzDist (μs n) μ) atTop (𝓝 0)) :
    WeaklyConverges atTop μs μ := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hb hl
  obtain ⟨L, hL⟩ := hl
  let f' : S →ᵇ ℝ := ⟨⟨f, hL.continuous⟩, hb⟩
  have hbound := fun n => integral_sub_le_boundedLipschitzDist (μs n) μ f' L hL
  have hzero : Tendsto (fun n => |(∫ x, f x ∂(μs n : Measure S)) -
      ∫ x, f x ∂(μ : Measure S)|) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => abs_nonneg _) hbound
    simpa using h.const_mul (‖f'‖ + L + 1)
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa [Real.dist_eq] using hzero)

/-- Zero distance separates arbitrary Borel probability laws, without tightness. -/
theorem boundedLipschitzDist_eq_zero_iff (μ ν : ProbabilityMeasure S) :
    boundedLipschitzDist μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    have hw := weaklyConverges_of_boundedLipschitzDist_sequence (fun _ => μ) ν
      (by simpa only [h] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    exact tendsto_nhds_unique tendsto_const_nhds hw
  · rintro rfl
    exact boundedLipschitzDist_self μ

/-- The metric structure is named, rather than installed globally, because
Mathlib's canonical topology on probability laws is the weak topology. -/
@[instance_reducible]
def boundedLipschitzMetric : MetricSpace (ProbabilityMeasure S) where
  dist := boundedLipschitzDist
  dist_self := boundedLipschitzDist_self
  dist_comm := boundedLipschitzDist_comm
  dist_triangle := boundedLipschitzDist_triangle
  eq_of_dist_eq_zero := (boundedLipschitzDist_eq_zero_iff _ _).mp

/-- Continuity into the weak topology holds on every metric state space.
Sequential continuity suffices here because the domain has the BL metric. -/
theorem boundedLipschitzMetric_continuous_id :
    @Continuous (ProbabilityMeasure S) (ProbabilityMeasure S)
      (boundedLipschitzMetric (S := S)).toUniformSpace.toTopologicalSpace
      (weakTopology (S := S)) id := by
  rw [weakTopology_eq]
  let : MetricSpace (ProbabilityMeasure S) := boundedLipschitzMetric
  let : TopologicalSpace (ProbabilityMeasure S) :=
    (boundedLipschitzMetric (S := S)).toUniformSpace.toTopologicalSpace
  apply (@continuous_iff_seqContinuous (ProbabilityMeasure S) (ProbabilityMeasure S)
    (boundedLipschitzMetric (S := S)).toUniformSpace.toTopologicalSpace
    ProbabilityMeasure.instTopologicalSpace inferInstance id).mpr
  intro μs μ h
  apply weaklyConverges_of_boundedLipschitzDist_sequence μs μ
  exact tendsto_iff_dist_tendsto_zero.mp h

/-- A finite real metric with exactly the source distance, whose topology
maps continuously to the weak topology. -/
theorem boundedLipschitzDist_metric_and_continuity :
    ∃ m : MetricSpace (ProbabilityMeasure S),
      (∀ μ ν, @dist _ m.toDist μ ν = boundedLipschitzDist μ ν) ∧
      @Continuous (ProbabilityMeasure S) (ProbabilityMeasure S)
        m.toUniformSpace.toTopologicalSpace (weakTopology (S := S)) id :=
  ⟨boundedLipschitzMetric, fun _ _ => rfl, boundedLipschitzMetric_continuous_id⟩

/-- Convergence in BL distance implies weak convergence for every filter,
including arbitrary nets. -/
theorem boundedLipschitzDist_tendsto_weak {ι : Type v} (l : Filter ι)
    (μs : ι → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (h : Tendsto (fun i => boundedLipschitzDist (μs i) μ) l (𝓝 0)) :
    WeaklyConverges l μs μ := by
  have hc := boundedLipschitzMetric_continuous_id (S := S)
  rw [weakTopology_eq] at hc
  let : MetricSpace (ProbabilityMeasure S) := boundedLipschitzMetric
  let : TopologicalSpace (ProbabilityMeasure S) :=
    (boundedLipschitzMetric (S := S)).toUniformSpace.toTopologicalSpace
  exact (@Continuous.tendsto (ProbabilityMeasure S) (ProbabilityMeasure S)
    (boundedLipschitzMetric (S := S)).toUniformSpace.toTopologicalSpace
    ProbabilityMeasure.instTopologicalSpace id hc μ).comp
      (tendsto_iff_dist_tendsto_zero.mpr h)

end
end ProbabilityFoundations.Ch06
