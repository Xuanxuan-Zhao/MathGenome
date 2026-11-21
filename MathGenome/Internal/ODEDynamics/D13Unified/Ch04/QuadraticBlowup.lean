import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.DerivativeCriterion
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.QuadraticBlowup
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch04.QuadraticBlowup
open Specs.D13Unified.Ch04.QuadraticBlowup

@[simp] lemma quadraticODE_eval (t x : ℝ) : quadraticODE.eval t x = x ^ 2 := by
  simp [ODE.eval, quadraticODE]

theorem regularity : regularityExpected := by
  have h : ContDiff ℝ ∞ (fun z : ℝ × ℝ => quadraticODE.eval z.1 z.2) := by
    simpa only [quadraticODE_eval] using (contDiff_snd.pow 2 :
      ContDiff ℝ ∞ (fun z : ℝ × ℝ => z.2 ^ 2))
  exact ⟨h, quadraticODE.locallyLipschitzInState_of_contDiffOn
    (h.of_le (by simp)).contDiffOn⟩

lemma curve_reciprocal (s ξ : ℝ) (hξ : ξ ≠ 0) (t : ℝ) :
    quadraticCurve s ξ t = (s + 1 / ξ - t)⁻¹ := by
  have hd : 1 - ξ * (t - s) = ξ * (s + 1 / ξ - t) := by
    field_simp
    ring
  rw [quadraticCurve, hd, div_eq_mul_inv, mul_inv_rev]
  calc
    ξ * ((s + 1 / ξ - t)⁻¹ * ξ⁻¹) = (ξ * ξ⁻¹) * (s + 1 / ξ - t)⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ hξ, one_mul]

lemma pole_right (b : ℝ) : Tendsto (fun t : ℝ => (b - t)⁻¹) (𝓝[<] b) atTop := by
  apply tendsto_inv_nhdsGT_zero.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun t : ℝ => b - t) (𝓝[<] b) (𝓝 (b - b)) :=
      tendsto_const_nhds.sub (tendsto_id'.mpr nhdsWithin_le_nhds)
    simpa only [sub_self] using h
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.mpr (show t < b from ht)

lemma pole_left (b : ℝ) : Tendsto (fun t : ℝ => (b - t)⁻¹) (𝓝[>] b) atBot := by
  apply tendsto_inv_nhdsLT_zero.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun t : ℝ => b - t) (𝓝[>] b) (𝓝 (b - b)) :=
      tendsto_const_nhds.sub (tendsto_id'.mpr nhdsWithin_le_nhds)
    simpa only [sub_self] using h
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_neg.mpr (show b < t from ht)

theorem endpoints : endpointExpected := by
  intro s ξ
  refine ⟨?_, ?_, ?_⟩
  · intro hξ
    simpa only [funext (curve_reciprocal s ξ hξ.ne')] using pole_right (s + 1 / ξ)
  · intro hξ
    simpa only [funext (curve_reciprocal s ξ hξ.ne)] using pole_left (s + 1 / ξ)
  · rintro rfl
    constructor
    · simp [quadraticInterval]
    · funext t
      simp [quadraticCurve]

theorem nonextension : nonextensionExpected := by
  intro s ξ hξ J y hy heq hb
  have hyb := (hy.continuousAt (J.isOpen.mem_nhds hb)).tendsto
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · have he : y =ᶠ[𝓝[>] (s + 1 / ξ)] quadraticCurve s ξ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact heq (by simpa [quadraticInterval, hneg, not_lt_of_gt hneg] using ht)
    exact not_tendsto_nhds_of_tendsto_atBot ((endpoints s ξ).2.1 hneg) (y (s + 1 / ξ))
      ((hyb.mono_left nhdsWithin_le_nhds).congr' he)
  · have he : y =ᶠ[𝓝[<] (s + 1 / ξ)] quadraticCurve s ξ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact heq (by simpa [quadraticInterval, hpos] using ht)
    exact not_tendsto_nhds_of_tendsto_atTop ((endpoints s ξ).1 hpos) (y (s + 1 / ξ))
      ((hyb.mono_left nhdsWithin_le_nhds).congr' he)

lemma initial_mem (s ξ : ℝ) : s ∈ (quadraticInterval s ξ).carrier := by
  rcases lt_trichotomy ξ 0 with hneg | rfl | hpos
  · simp [quadraticInterval, hneg, not_lt_of_gt hneg]
  · simp [quadraticInterval]
  · simp [quadraticInterval, hpos]

lemma pole_ne_on_interval (s ξ : ℝ) (hξ : ξ ≠ 0) {t : ℝ}
    (ht : t ∈ (quadraticInterval s ξ).carrier) : s + 1 / ξ - t ≠ 0 := by
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · have ht' : s + 1 / ξ < t := by
      simpa [quadraticInterval, hneg, not_lt_of_gt hneg] using ht
    linarith
  · have ht' : t < s + 1 / ξ := by simpa [quadraticInterval, hpos] using ht
    linarith

lemma curve_hasDerivAt (s ξ : ℝ) {t : ℝ}
    (ht : t ∈ (quadraticInterval s ξ).carrier) :
    HasDerivAt (quadraticCurve s ξ) (quadraticCurve s ξ t ^ 2) t := by
  by_cases hξ : ξ = 0
  · subst ξ
    have hz : quadraticCurve s 0 = fun _ => 0 := by
      funext r; simp [quadraticCurve]
    rw [hz]
    simpa using hasDerivAt_const t (0 : ℝ)
  · rw [show quadraticCurve s ξ = (fun t => (s + 1 / ξ - t)⁻¹) from
      funext (curve_reciprocal s ξ hξ)]
    convert ((hasDerivAt_const t (s + 1 / ξ)).sub (hasDerivAt_id t)).inv
      (pole_ne_on_interval s ξ hξ ht) using 1 <;> first | rfl | simp [one_div, inv_pow]

lemma explicit_ivp (s ξ : ℝ) :
    IsClassicalIVPOn quadraticODE (quadraticInterval s ξ) (quadraticCurve s ξ) s ξ := by
  refine ⟨(classical_iff_solutionOn _ _ _).mpr ?_, initial_mem s ξ, ?_⟩
  · refine ⟨?_, fun _ _ => mem_univ _, ?_⟩
    · intro t ht
      exact (curve_hasDerivAt s ξ ht).continuousAt.continuousWithinAt
    · intro t ht
      simpa only [quadraticODE_eval] using (curve_hasDerivAt s ξ ht).hasDerivWithinAt
  · simp [quadraticCurve]

/-- The maximal solution cannot cross the pole, so the explicit pole-free
interval is exactly the interval selected by the upstream maximal construction. -/
theorem solution : solutionExpected := by
  intro s ξ
  have hF := regularity.2
  obtain ⟨hc, hcs, hcξ, hmax, hep, hrestrict, huniq⟩ :=
    ODE.canonical_solution quadraticODE hF s ξ (mem_univ _)
  obtain ⟨hsub, heq⟩ := hrestrict (quadraticInterval s ξ) (quadraticCurve s ξ)
    (explicit_ivp s ξ)
  have hdom :
      (Specs.D13Unified.Ch04.MaximalSolutionMap.maximalIntervalValue quadraticODE s ξ).carrier =
        (quadraticInterval s ξ).carrier := by
    apply Subset.antisymm ?_ hsub
    intro t ht
    by_cases hξ : ξ = 0
    · subst ξ
      simp [quadraticInterval]
    · have hnp := nonextension s ξ hξ
        (Specs.D13Unified.Ch04.MaximalSolutionMap.maximalIntervalValue quadraticODE s ξ)
        (Specs.D13Unified.Ch04.MaximalSolutionMap.solutionCurveValue quadraticODE s ξ)
        hc.1.continuousOn heq
      rcases lt_or_gt_of_ne hξ with hneg | hpos
      · have hs' : s + 1 / ξ < s := by linarith [one_div_neg.mpr hneg]
        have ht' : s + 1 / ξ < t := by
          by_contra h
          exact hnp ((Specs.D13Unified.Ch04.MaximalSolutionMap.maximalIntervalValue
            quadraticODE s ξ).ordConnected.out ht hcs ⟨le_of_not_gt h, hs'.le⟩)
        simpa [quadraticInterval, hneg, not_lt_of_gt hneg] using ht'
      · have hs' : s < s + 1 / ξ := by linarith [one_div_pos.mpr hpos]
        have ht' : t < s + 1 / ξ := by
          by_contra h
          exact hnp ((Specs.D13Unified.Ch04.MaximalSolutionMap.maximalIntervalValue
            quadraticODE s ξ).ordConnected.out hcs ht ⟨hs'.le, le_of_not_gt h⟩)
        simpa [quadraticInterval, hpos] using ht'
  refine ⟨explicit_ivp s ξ, hdom, heq, ?_⟩
  intro J y hy
  obtain ⟨hJ, hey⟩ := hrestrict J y hy
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [← hdom]
    exact hJ ht
  · intro t ht
    exact (hey ht).symm.trans (heq (by rw [← hdom]; exact hJ ht))

theorem maximality : maximalityExpected := by
  intro s ξ
  let x : Solution quadraticODE :=
    ⟨quadraticInterval s ξ, quadraticCurve s ξ, (explicit_ivp s ξ).1⟩
  have hall := (solution s ξ).2.2.2
  have hx : Specs.D13Unified.Ch01.SolutionConcepts.maximalValue x := by
    rintro ⟨y, hxy, hstrict⟩
    have hy : IsClassicalIVPOn quadraticODE y.interval y.representative s ξ :=
      ⟨y.isSolution, hxy.1 (initial_mem s ξ),
        (hxy.2 (initial_mem s ξ)).trans (explicit_ivp s ξ).2.2⟩
    exact hstrict.not_subset (hall y.interval y.representative hy).1
  refine ⟨⟨(explicit_ivp s ξ).1, hx⟩, ?_⟩
  intro y hsy hyξ hmy
  obtain ⟨hsub, heq⟩ := hall y.interval y.representative ⟨y.isSolution, hsy, hyξ⟩
  refine ⟨?_, heq⟩
  apply Subset.antisymm hsub
  by_contra hn
  exact hmy ⟨x, ⟨hsub, heq.symm⟩, ⟨hsub, hn⟩⟩

end D13Unified.Ch04.QuadraticBlowup
