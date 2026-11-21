import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakMetrics
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ProkhorovMetric

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityFoundations.Ch06

universe u v
noncomputable section
variable {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- The library's finite extended distance gives exactly the source's radius inequalities. -/
theorem prokhorovAdmissible_of_levyProkhorovDist_lt
    (μ ν : ProbabilityMeasure S) (a : ℝ)
    (ha : levyProkhorovDist (μ : Measure S) (ν : Measure S) < a) :
    ProkhorovAdmissible μ ν a := by
  have hpos : 0 < a := ENNReal.toReal_nonneg.trans_lt ha
  have he : levyProkhorovEDist (μ : Measure S) (ν : Measure S) < ENNReal.ofReal a := by
    exact (ENNReal.toReal_lt_toReal (levyProkhorovEDist_ne_top _ _) ENNReal.ofReal_ne_top).mp
      (by simpa [levyProkhorovDist, ENNReal.toReal_ofReal hpos.le] using ha)
  refine ⟨hpos, fun A hA => ⟨?_, ?_⟩⟩
  · have h := left_measure_le_of_levyProkhorovEDist_lt he hA
    have hr := ENNReal.toReal_mono (show
      (ν : Measure S) (Metric.thickening (ENNReal.ofReal a).toReal A) +
        ENNReal.ofReal a ≠ ∞ from by finiteness) h
    simpa [Measure.real, ENNReal.toReal_add, ENNReal.toReal_ofReal hpos.le,
      enlargement_eq_thickening] using hr
  · have h := right_measure_le_of_levyProkhorovEDist_lt he hA
    have hr := ENNReal.toReal_mono (show
      (μ : Measure S) (Metric.thickening (ENNReal.ofReal a).toReal A) +
        ENNReal.ofReal a ≠ ∞ from by finiteness) h
    simpa [Measure.real, ENNReal.toReal_add, ENNReal.toReal_ofReal hpos.le,
      enlargement_eq_thickening] using hr

/-- Identification of the positive real infimum with Mathlib's extended infimum. -/
theorem prokhorovDist_eq_levyProkhorovDist (μ ν : ProbabilityMeasure S) :
    prokhorovDist μ ν = levyProkhorovDist (μ : Measure S) (ν : Measure S) := by
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    exact prokhorovDist_le_of_admissible μ ν a
      (prokhorovAdmissible_of_levyProkhorovDist_lt μ ν a ha)
  · apply le_csInf ⟨1, prokhorovAdmissible_one μ ν⟩
    intro a ha
    have he : levyProkhorovEDist (μ : Measure S) (ν : Measure S) ≤ ENNReal.ofReal a := by
      apply sInf_le
      intro A hA
      rcases ha.2 A hA with ⟨h₁, h₂⟩
      constructor
      · apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)).mp
        simpa [Measure.real, ENNReal.toReal_add, ENNReal.toReal_ofReal ha.1.le,
          enlargement_eq_thickening] using h₁
      · apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)).mp
        simpa [Measure.real, ENNReal.toReal_add, ENNReal.toReal_ofReal ha.1.le,
          enlargement_eq_thickening] using h₂
    simpa [levyProkhorovDist, ENNReal.toReal_ofReal ha.1.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he

/-- A metric on the original law space, without changing its global weak topology. -/
@[instance_reducible] def prokhorovMetricSpace : MetricSpace (ProbabilityMeasure S) :=
  MetricSpace.induced (LevyProkhorov.ofMeasure : ProbabilityMeasure S →
    LevyProkhorov (ProbabilityMeasure S))
    (fun _ _ h => congrArg LevyProkhorov.toMeasure h) inferInstance

/-- The transported metric has exactly the source distance. -/
theorem prokhorovMetricSpace_dist (μ ν : ProbabilityMeasure S) :
    @dist _ (prokhorovMetricSpace (S := S)).toDist μ ν = prokhorovDist μ ν :=
  (prokhorovDist_eq_levyProkhorovDist μ ν).symm

theorem prokhorovDist_nonneg (μ ν : ProbabilityMeasure S) : 0 ≤ prokhorovDist μ ν :=
  (prokhorovDist_bounds μ ν).1

@[simp] theorem prokhorovDist_self (μ : ProbabilityMeasure S) :
    prokhorovDist μ μ = 0 := by
  rw [prokhorovDist_eq_levyProkhorovDist, levyProkhorovDist_self]

theorem prokhorovDist_comm (μ ν : ProbabilityMeasure S) :
    prokhorovDist μ ν = prokhorovDist ν μ := by
  simp only [prokhorovDist_eq_levyProkhorovDist, levyProkhorovDist_comm]

@[simp] theorem prokhorovDist_eq_zero_iff (μ ν : ProbabilityMeasure S) :
    prokhorovDist μ ν = 0 ↔ μ = ν := by
  let := prokhorovMetricSpace (S := S)
  rw [← prokhorovMetricSpace_dist]
  exact dist_eq_zero

theorem prokhorovDist_triangle (μ ν κ : ProbabilityMeasure S) :
    prokhorovDist μ κ ≤ prokhorovDist μ ν + prokhorovDist ν κ := by
  simp only [prokhorovDist_eq_levyProkhorovDist]
  exact levyProkhorovDist_triangle _ _ _

/-- The identity from π's metric topology to the initial weak topology is continuous. -/
theorem prokhorov_continuous_identity :
    @Continuous (ProbabilityMeasure S) (ProbabilityMeasure S)
      (prokhorovMetricSpace (S := S)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (weakTopology (S := S)) id := by
  rw [weakTopology_eq]
  exact @Continuous.comp (ProbabilityMeasure S)
    (LevyProkhorov (ProbabilityMeasure S)) (ProbabilityMeasure S)
    (prokhorovMetricSpace (S := S)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    inferInstance inferInstance LevyProkhorov.ofMeasure LevyProkhorov.toMeasure
    LevyProkhorov.continuous_toMeasure_probabilityMeasure continuous_induced_dom

/-- Metric convergence implies weak convergence along every filter, including nets. -/
theorem weaklyConverges_of_prokhorovDist_tendsto {ι : Type v}
    (l : Filter ι) (μs : ι → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (h : Tendsto (fun i => prokhorovDist (μs i) μ) l (𝓝 0)) :
    WeaklyConverges l μs μ := by
  have hc := prokhorov_continuous_identity (S := S)
  rw [weakTopology_eq] at hc
  have hm : Tendsto μs l
      (@nhds _ (prokhorovMetricSpace (S := S)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace μ) := by
    let := prokhorovMetricSpace (S := S)
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [prokhorovMetricSpace_dist] using h
  exact Filter.Tendsto.comp (f := μs) (g := id) (@Continuous.continuousAt (ProbabilityMeasure S) (ProbabilityMeasure S)
    (prokhorovMetricSpace (S := S)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    inferInstance id μ hc) hm

end
end ProbabilityFoundations.Ch06
