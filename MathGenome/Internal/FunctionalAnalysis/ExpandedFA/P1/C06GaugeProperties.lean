import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06Gauge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Sublinear
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06GaugeProperties

/-! Gauge and continuity, paper.tex:1048–1081 (`fa2:p1:c06:gauge-properties`). The bridge to Mathlib's gauge
is definitional: both take the real infimum over the same positive dilations.
The algebraic part uses exactly the paper's one-positive-dilation absorption. -/
namespace ExpandedFA.P1.C06
open scoped Topology Pointwise
open Filter
universe u v

section Algebraic
variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Identifies the actual defining formulas, including the empty-set convention. -/
theorem minkowskiGauge_eq_gauge (U : Set E) : minkowskiGauge U = gauge U := rfl

theorem minkowskiGauge_finite (U : Set E) (hU : GaugeAdmissible U) (x : E) :
    IsGLB (gaugeScales U x) (minkowskiGauge U x) ∧
      ∃ t : ℝ, 0 < t ∧ x ∈ t • U ∧ minkowskiGauge U x ≤ t := by
  refine ⟨minkowskiGauge_isGLB U hU.1 x, ?_⟩
  obtain ⟨t, ht, hx⟩ := hU.1 x
  exact ⟨t, ht, hx, gauge_le_of_mem ht.le hx⟩

theorem minkowskiGauge_nonneg (U : Set E) (_hU : GaugeAdmissible U) (x : E) :
    0 ≤ minkowskiGauge U x := gauge_nonneg x

theorem minkowskiGauge_zero (U : Set E) (_hU : GaugeAdmissible U) :
    minkowskiGauge U 0 = 0 := gauge_zero

theorem minkowskiGauge_smul_nonneg (U : Set E) (_hU : GaugeAdmissible U)
    (t : ℝ) (ht : 0 ≤ t) (x : E) :
    minkowskiGauge U (t • x) = t * minkowskiGauge U x :=
  gauge_smul_of_nonneg ht x

/-- Direct infimum argument, avoiding an unproved conversion from positive
absorption to Mathlib's absorption by all sufficiently large signed scalars. -/
theorem minkowskiGauge_add_le (U : Set E) (hU : GaugeAdmissible U) (x y : E) :
    minkowskiGauge U (x + y) ≤ minkowskiGauge U x + minkowskiGauge U y := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ⟨ha, u, hu, hux⟩, ha'⟩ :=
    exists_lt_of_csInf_lt (hU.1 x) (lt_add_of_pos_right (minkowskiGauge U x) (half_pos hε))
  obtain ⟨b, ⟨hb, v, hv, hvy⟩, hb'⟩ :=
    exists_lt_of_csInf_lt (hU.1 y) (lt_add_of_pos_right (minkowskiGauge U y) (half_pos hε))
  have hxy : x + y ∈ (a + b) • U := by
    rw [hU.2.1.add_smul ha.le hb.le, ← hux, ← hvy]
    exact Set.add_mem_add (Set.smul_mem_smul_set hu) (Set.smul_mem_smul_set hv)
  have hle : minkowskiGauge U (x + y) ≤ a + b := gauge_le_of_mem (by positivity) hxy
  linarith

theorem minkowskiGauge_sublinear (U : Set E) (hU : GaugeAdmissible U) :
    ExpandedFA.P1.IsSublinear (minkowskiGauge U) :=
  ⟨minkowskiGauge_add_le U hU, minkowskiGauge_smul_nonneg U hU⟩
end Algebraic

section Topological
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

set_option linter.unusedSectionVars false in
theorem minkowskiGauge_open_unit (U : Set E) (hc : Convex ℝ U)
    (h0 : (0 : E) ∈ U) (ho : IsOpen U) : U = {x | minkowskiGauge U x < 1} :=
  (setOfPred_gauge_lt_one_eq_self_of_isOpen hc h0 ho).symm

theorem minkowskiGauge_continuous (U : Set E) (hc : Convex ℝ U)
    (h0 : (0 : E) ∈ U) (ho : IsOpen U) : Continuous (minkowskiGauge U) :=
  continuous_gauge hc (ho.mem_nhds h0)

theorem continuous_of_le_minkowskiGauge (U : Set E) (hc : Convex ℝ U)
    (h0 : (0 : E) ∈ U) (ho : IsOpen U) (h : E →ₗ[ℝ] ℝ)
    (hh : ∀ x, h x ≤ minkowskiGauge U x) : Continuous h := by
  have hp := minkowskiGauge_continuous U hc h0 ho
  have hu : Tendsto (minkowskiGauge U) (𝓝 0) (𝓝 0) := by
    simpa only [minkowskiGauge_eq_gauge, gauge_zero] using hp.continuousAt.tendsto (x := 0)
  have hl : Tendsto (fun x : E => -minkowskiGauge U (-x)) (𝓝 0) (𝓝 0) := by
    have H : Continuous (fun x : E => -minkowskiGauge U (-x)) :=
      continuous_neg.comp (hp.comp continuous_neg)
    convert H.continuousAt.tendsto (x := 0) using 1
    simp [minkowskiGauge_eq_gauge]
  have ht : Tendsto h (𝓝 0) (𝓝 0) := hl.squeeze hu (fun x => by
    simpa only [map_neg, neg_neg] using neg_le_neg (hh (-x))) hh
  exact continuous_of_tendsto_nhds_zero h ht
end Topological

theorem minkowskiGauge_continuous_seminorm
    {𝕜 : Type v} [RCLike 𝕜] {E : Type u} [AddCommGroup E]
    [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [ContinuousSMul 𝕜 E] (U : Set E) (hc : Convex ℝ U)
    (h0 : (0 : E) ∈ U) (ho : IsOpen U) (hb : Balanced 𝕜 U) :
    (∃ p : Seminorm 𝕜 E, (∀ x, p x = minkowskiGauge U x) ∧ Continuous (p : E → ℝ)) ∧
      (∀ a : 𝕜, ∀ x : E, minkowskiGauge U (a • x) = ‖a‖ * minkowskiGauge U x) := by
  refine ⟨⟨gaugeSeminorm hb hc (absorbent_nhds_zero (ho.mem_nhds h0)), ?_, ?_⟩, ?_⟩
  · intro x; rfl
  · exact continuous_gauge hc (ho.mem_nhds h0)
  · exact gauge_smul hb

/-- Explicit complex specialization using continuity of the restricted scalar
 action, valid without Hausdorffness or local convexity. -/
theorem minkowskiGauge_complex_continuous_seminorm
    {E : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (U : Set E) (hc : Convex ℝ U) (h0 : (0 : E) ∈ U)
    (ho : IsOpen U) (hb : Balanced ℂ U) :
    (∃ p : Seminorm ℂ E, (∀ x, p x = minkowskiGauge U x) ∧ Continuous (p : E → ℝ)) ∧
      (∀ a : ℂ, ∀ x : E, minkowskiGauge U (a • x) = ‖a‖ * minkowskiGauge U x) := by
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact minkowskiGauge_continuous_seminorm U hc h0 ho hb

theorem minkowskiGauge_norm_bound {E : Type u} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (U : Set E) (r : ℝ) (hr : 0 < r)
    (hU : Metric.ball (0 : E) r ⊆ U) (x : E) : minkowskiGauge U x ≤ ‖x‖ / r := by
  change gauge U x ≤ ‖x‖ / r
  exact (le_div_iff₀ hr).2 (by simpa only [mul_comm] using (mul_gauge_le_norm hU (x := x)))

theorem minkowskiGauge_complex_norm_bound {E : Type u} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    ∀ (U : Set E) (r : ℝ), 0 < r → Metric.ball (0 : E) r ⊆ U →
      ∀ x : E, minkowskiGauge U x ≤ ‖x‖ / r := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  exact minkowskiGauge_norm_bound

end ExpandedFA.P1.C06
