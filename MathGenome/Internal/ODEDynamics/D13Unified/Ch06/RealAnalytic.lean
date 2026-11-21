import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.RealAnalytic
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.RealAnalyticPropagation

/-! Real-analytic dependence on the full real maximal domain
(`paper.tex`, d13:06:real-analytic). The local bridge constructs the
complexification, proves reality and identifies the restriction with the
original canonical real IVP. Propagation then uses real rebasing and
composition on the connected maximal interval, retaining all moving data. -/
noncomputable section
namespace D13Unified.Ch06.RealAnalytic
open Set Metric

/-- Local absolutely convergent coordinate series supply open neighborhoods. -/
theorem CoordinateRealAnalyticOn.isOpen {d n : ℕ} {V : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → Fin n → ℝ} (hf : CoordinateRealAnalyticOn V f) : IsOpen V := by
  apply Metric.isOpen_iff.mpr
  intro a ha
  obtain ⟨r, hr, hV, _⟩ := hf a ha
  exact ⟨r, hr, hV⟩

/-- Joint real analyticity in terminal time, initial time, state and
parameters at every point of the actual canonical maximal solution domain. -/
theorem real_analytic_dependence :
    Specs.D13Unified.Ch06.RealAnalytic.realAnalyticDependence_type := by
  intro n m F hF
  refine ⟨analytic_solution_domain_open F hF, ?_⟩
  exact D13Unified.Ch06.RealAnalyticPropagation.real_analytic_propagation F
    (analytic_field_locallyLipschitz F hF) (local_real_analytic_dependence F hF)

end D13Unified.Ch06.RealAnalytic
