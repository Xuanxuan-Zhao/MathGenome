import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.StrictFatouExample
import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral

/-! The mass escaping to infinity example of paper.tex:1743–1755.
All integral values are in `ℝ≥0∞`. The completed one-dimensional Lebesgue
measure and the finite-simple-minorant integral are reused from the shared
interfaces. The only measure calculation is the normalization of [n,n+1).
-/

open Set Filter MeasureTheory D11.Ch03
open scoped Topology ENNReal
noncomputable section

namespace D11.Ch05.StrictFatouExample

local instance : MeasurableSpace ℝ := realLebesgueSpace
local instance : MeasurableSpace (D11.Ch03.Point 1) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1

lemma coordinate_measurable : Measurable lineEquiv.symm := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  have heq : lineEquiv.symm ⁻¹' (lineEquiv ⁻¹' t) = t := by
    ext x
    simp
  rwa [heq]

lemma interval_preimage (a b : ℝ) :
    lineEquiv.symm ⁻¹' Ico a b =
      D11.Ch03.endpointBox (fun _ => a) (fun _ => b) (fun _ => true) (fun _ => false) := by
  ext x
  change (a ≤ x 0 ∧ x 0 < b) ↔ _
  simp only [D11.Ch03.endpointBox, mem_ofPred_eq,
    ite_true, Bool.false_eq_true, ite_false]
  exact ⟨fun h i => by simpa only [Subsingleton.elim i (0 : Fin 1)] using h,
    fun h => h 0⟩

lemma interval_measurable (a b : ℝ) : MeasurableSet (Ico a b) := by
  refine ⟨D11.Ch03.endpointBox (fun _ => a) (fun _ => b)
    (fun _ => true) (fun _ => false), ?_, ?_⟩
  · exact LebesgueMeasures.borel_le_lebesgue 1 _
      (LebesgueMeasures.endpointBox_borel 1 _ _ _ _)
  · ext x
    simp [D11.Ch03.endpointBox, lineEquiv]

theorem interval_measure (a b : ℝ) :
    realLebesgue (Ico a b) = ENNReal.ofReal (b - a) := by
  rw [realLebesgue, Measure.map_apply coordinate_measurable (interval_measurable a b),
    interval_preimage]
  rw [LebesgueMeasures.lebesgue_box]
  simp [D11.Ch03.boxContent]

theorem measurable_escaping (n : ℕ) : Measurable (escaping n) := by
  exact measurable_const.indicator (interval_measurable _ _)

theorem eventually_zero (x : ℝ) : ∀ᶠ n : ℕ in atTop, escaping n x = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  filter_upwards [eventually_ge_atTop N] with n hn
  apply indicator_of_notMem
  intro hx
  have hnx : (n : ℝ) ≤ x := hx.1
  have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  exact (not_le_of_gt hN) (hNn.trans hnx)

theorem pointwise_tendsto (x : ℝ) :
    Tendsto (fun n => escaping n x) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_zero x] with n hn
  exact hn.symm

theorem pointwise_liminf (x : ℝ) :
    liminf (fun n => escaping n x) atTop = 0 := by
  exact (pointwise_tendsto x).liminf_eq

theorem integral_each (n : ℕ) :
    NonnegativeIntegral.nonnegativeIntegral realLebesgue (escaping n) = 1 := by
  rw [NonnegativeIntegral.integral_eq_lintegral]
  rw [escaping, lintegral_indicator (interval_measurable _ _)]
  simp [interval_measure]

theorem integral_liminf_zero :
    NonnegativeIntegral.nonnegativeIntegral realLebesgue
      (fun x => liminf (fun n => escaping n x) atTop) = 0 := by
  simp_rw [pointwise_liminf]
  rw [NonnegativeIntegral.integral_eq_lintegral]
  simp

theorem liminf_integral_one :
    liminf (fun n => NonnegativeIntegral.nonnegativeIntegral realLebesgue (escaping n))
      atTop = 1 := by
  simp_rw [integral_each]
  exact tendsto_const_nhds.liminf_eq

theorem strict_fatou : Specs.D11.Ch05.StrictFatouExample.strict_fatou :=
  ⟨integral_liminf_zero, zero_lt_one, liminf_integral_one.symm⟩

theorem strict_inequality :
    NonnegativeIntegral.nonnegativeIntegral realLebesgue
      (fun x => liminf (fun n => escaping n x) atTop) <
    liminf (fun n => NonnegativeIntegral.nonnegativeIntegral realLebesgue (escaping n))
      atTop := by
  rw [integral_liminf_zero, liminf_integral_one]
  exact zero_lt_one

theorem integrals_not_tendsto_zero :
    ¬ Tendsto (fun n => NonnegativeIntegral.nonnegativeIntegral realLebesgue (escaping n))
      atTop (𝓝 0) := by
  intro h
  have h01 : (0 : ℝ≥0∞) = 1 := h.liminf_eq.symm.trans liminf_integral_one
  exact zero_ne_one h01

end D11.Ch05.StrictFatouExample
