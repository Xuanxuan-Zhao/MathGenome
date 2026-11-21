import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.RealTraceDeterminantContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.RealExteriorDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.TraceDeterminantContinuity

noncomputable section
universe v w
namespace ExpandedFA.FredholmDeterminant.RealTraceDeterminantContinuity
open RealExteriorDefinitions
open TraceIdeals.TraceClassDefinitions.Spec
open Filter
open scoped Topology

namespace RC
open TraceIdeals.RealComplexification

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := Spec.completeSpace

omit [CompleteSpace H] in
/-- Complexification commutes with the difference appearing in the real trace norm. -/
lemma operator_sub (S T : H →L[ℝ] H) : operator (S - T) = operator S - operator T := by
  ext p; rfl

lemma traceNorm_operator (T : H →L[ℝ] H) (hT : IsTraceClassValue T) :
    TraceNormValue (operator T) = TraceNormValue T :=
  (trace_ideal H H T).2 hT

end RC

open TraceIdeals.RealComplexification
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

theorem entire_exterior_series : Spec.EntireExteriorSeries.{v} := by
  intro H _ _ _ T hT
  refine ⟨complex_series_summable T hT, ?_⟩
  have heq : complexParameterDeterminant T =
      TraceClassDefinitions.Spec.FredholmDeterminantValue (operator T) :=
    funext (determinant_complexification T hT)
  change Differentiable ℂ (complexParameterDeterminant T)
  rw [heq]
  exact (TraceDeterminantContinuity.entire_exterior_series (operator T)
    ((traceClass_operator_iff T).mpr hT)).2

theorem uniform_exterior_series : Spec.UniformExteriorSeries.{v} := by
  intro H _ _ _ T hT R hR
  have h := TraceDeterminantContinuity.uniform_exterior_series (operator T)
    ((traceClass_operator_iff T).mpr hT) R hR
  have heq : TraceClassDefinitions.Spec.FredholmDeterminantValue (operator T) =
      complexParameterDeterminant T := (funext (determinant_complexification T hT)).symm
  simpa only [← coefficient_cast T hT, heq] using h

theorem parameter_perturbation_bound : Spec.ParameterPerturbationBound.{v} := by
  intro H _ _ _ S T hS hT z
  have h := TraceDeterminantContinuity.parameter_perturbation_bound (operator S) (operator T)
    ((traceClass_operator_iff S).mpr hS) ((traceClass_operator_iff T).mpr hT) z
  rw [← RC.operator_sub, RC.traceNorm_operator (T - S)
    (TraceIdeals.TraceNormIdeal.traceClass_sub T S hT hS),
    RC.traceNorm_operator T hT, RC.traceNorm_operator S hS,
    ← determinant_complexification T hT, ← determinant_complexification S hS] at h
  exact h

theorem determinant_perturbation_bound : Spec.DeterminantPerturbationBound.{v} := by
  intro H _ _ _ S T hS hT
  have h := parameter_perturbation_bound S T hS hT 1
  change ‖complexParameterDeterminant T 1 - complexParameterDeterminant S 1‖ ≤
    ‖(1 : ℂ)‖ * TraceNormValue (T - S) *
      Real.exp (‖(1 : ℂ)‖ * max (TraceNormValue T) (TraceNormValue S)) at h
  rw [← Complex.ofReal_one, determinant_real_parameter, determinant_real_parameter,
    ← Complex.ofReal_sub, Complex.norm_real] at h
  simpa only [Complex.ofReal_one, norm_one, one_mul] using h

theorem traceNorm_locally_uniform : Spec.TraceNormLocallyUniform.{v,w} := by
  intro H _ _ _ I l T L hT hL hlim
  have hlimC : Tendsto (fun i => TraceNormValue (operator (T i) - operator L)) l (𝓝 0) := by
    simpa only [← RC.operator_sub, RC.traceNorm_operator _
      (TraceIdeals.TraceNormIdeal.traceClass_sub _ _ (hT _) hL)] using hlim
  have hc := TraceDeterminantContinuity.traceNorm_locally_uniform l (fun i => operator (T i))
    (operator L) (fun i => (traceClass_operator_iff _).mpr (hT i))
    ((traceClass_operator_iff L).mpr hL) hlimC
  have hd : ∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
      (fun i => complexParameterDeterminant (T i)) (complexParameterDeterminant L)
      l (Metric.closedBall 0 R) := by
    intro R hR
    have heqT : (fun i => TraceClassDefinitions.Spec.FredholmDeterminantValue (operator (T i))) =
        (fun i => complexParameterDeterminant (T i)) :=
      funext (fun i => (funext (determinant_complexification (T i) (hT i))).symm)
    have heqL : TraceClassDefinitions.Spec.FredholmDeterminantValue (operator L) =
        complexParameterDeterminant L := (funext (determinant_complexification L hL)).symm
    simpa only [heqT, heqL] using hc R hR
  exact ⟨hd, TraceDeterminantContinuity.locallyUniform_of_disks hd⟩

/-- Real parameters and values retain the same distances under the canonical inclusion. -/
lemma real_uniform_of_complex {I : Type w} {l : Filter I}
    (T : I → H →L[ℝ] H) (L : H →L[ℝ] H) {R : ℝ}
    (h : TendstoUniformlyOn (fun i => complexParameterDeterminant (T i))
      (complexParameterDeterminant L) l (Metric.closedBall 0 R)) :
    TendstoUniformlyOn (fun i => realDeterminant (T i)) (realDeterminant L)
      l (Metric.closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with i hi
  intro r hr
  have hrC : (r : ℂ) ∈ Metric.closedBall 0 R := by
    simpa only [mem_closedBall_zero_iff, Complex.norm_real] using hr
  have hh := hi (r : ℂ) hrC
  simpa only [determinant_real_parameter, dist_eq_norm, ← Complex.ofReal_sub,
    Complex.norm_real] using hh

theorem real_traceNorm_locally_uniform : Spec.RealTraceNormLocallyUniform.{v,w} := by
  intro H _ _ _ I l T L hT hL hlim
  have hc := (traceNorm_locally_uniform l T L hT hL hlim).1
  have hd : ∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
      (fun i => realDeterminant (T i)) (realDeterminant L) l (Metric.closedBall 0 R) :=
    fun R hR => real_uniform_of_complex T L (hc R hR)
  refine ⟨hd, ?_⟩
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro r
  refine ⟨Metric.closedBall 0 (‖r‖ + 1), ?_, hd _ (by positivity)⟩
  exact Metric.closedBall_mem_nhds_of_mem (by simp)

theorem determinant_multiplicative : Spec.DeterminantMultiplicative.{v} := by
  intro H _ _ _ S T hS hT
  have hc := TraceDeterminantContinuity.determinant_multiplicative (operator S) (operator T)
    ((traceClass_operator_iff S).mpr hS) ((traceClass_operator_iff T).mpr hT)
  have hop : operator (S + T + S.comp T) =
      operator S + operator T + (operator S).comp (operator T) := by simp
  have hU : IsTraceClassValue (S + T + S.comp T) :=
    (traceClass_operator_iff _).mp (hop.symm ▸ hc.1)
  refine ⟨hU, ?_, ?_⟩
  · ext x
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.id_apply, map_add]
    abel
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, ← determinant_real_parameter, ← determinant_real_parameter,
      ← determinant_real_parameter]
    simp only [Complex.ofReal_one, determinant_complexification _ hU,
      determinant_complexification _ hS, determinant_complexification _ hT, hop]
    exact hc.2

end ExpandedFA.FredholmDeterminant.RealTraceDeterminantContinuity
