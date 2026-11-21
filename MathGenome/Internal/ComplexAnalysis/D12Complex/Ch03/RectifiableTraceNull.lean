import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.RectifiableTraceNull
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.ArclengthFactorization
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! A finite-length continuous path has planar Lebesgue measure zero.
The upstream arclength factor is Lipschitz on a real interval, even when
the length is zero. Thus its image has Hausdorff dimension at most one.
Two-dimensional Hausdorff measure is an additive Haar measure on ℂ, so
Lebesgue measure is absolutely continuous with respect to it. This proves
the actual planar nullity before deducing the topological conclusion. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal MeasureTheory

namespace D12Complex.RectifiableTrace
open Stieltjes

theorem trace_volume_zero :
    Specs.D12Complex.Ch03.RectifiableTraceNull.trace_volume_zero_type := by
  intro γ hγ
  obtain ⟨σ, hlip, _, htrace, _⟩ := Arclength.lipschitz_factor γ hγ
  have hdim : dimH γ.trace ≤ 1 := by
    rw [← htrace]
    calc
      dimH (σ '' Icc 0 (polygonalLength γ).toReal) ≤
          dimH (Icc 0 (polygonalLength γ).toReal) := hlip.dimH_image_le
      _ ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
      _ = 1 := Real.dimH_univ
  have hac : (volume : Measure ℂ) ≪ Measure.hausdorffMeasure 2 := by
    simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using
      (Measure.absolutelyContinuous_isAddHaarMeasure (volume : Measure ℂ)
        (Measure.hausdorffMeasure (Module.finrank ℝ ℂ)))
  exact measure_zero_of_dimH_lt (d := 2) hac (hdim.trans_lt (by norm_num))

theorem trace_interior_empty :
    Specs.D12Complex.Ch03.RectifiableTraceNull.trace_interior_empty_type := by
  intro γ hγ
  exact volume.interior_eq_empty_of_null (trace_volume_zero γ hγ)

theorem finite_union_volume_zero :
    Specs.D12Complex.Ch03.RectifiableTraceNull.finite_union_volume_zero_type := by
  intro ι s γ hγ
  exact (measure_biUnion_null_iff s.countable_toSet).mpr
    (fun i hi => trace_volume_zero (γ i) (hγ i hi))

theorem finite_union_interior_empty :
    Specs.D12Complex.Ch03.RectifiableTraceNull.finite_union_interior_empty_type := by
  intro ι s γ hγ
  exact volume.interior_eq_empty_of_null (finite_union_volume_zero s γ hγ)

end D12Complex.RectifiableTrace
