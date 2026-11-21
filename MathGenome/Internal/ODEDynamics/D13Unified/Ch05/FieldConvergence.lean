import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.FieldConvergence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.CommonInterval
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D13Unified.Ch05.FieldConvergence
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
universe u

/-- Locally uniform convergence of fields gives persistence and uniform
convergence on every compact part of the limiting maximal interval. -/
theorem field_convergence :
    Specs.D13Unified.Ch05.FieldConvergence.fieldConvergenceExpected.{u} := by
  intro E _ _ _ F G hF hdom hG hconv s ξ sj ξj hs hdata a b has hsb hI
  obtain ⟨hx, hsI, hxs, _⟩ := ODE.canonical_solution F hF s ξ hs
  let x := solutionCurveValue F s ξ
  change x s = ξ at hxs
  have hsj : Tendsto sj atTop (𝓝 s) := (continuous_fst.tendsto (s, ξ)).comp hdata
  have hξj : Tendsto ξj atTop (𝓝 ξ) := (continuous_snd.tendsto (s, ξ)).comp hdata
  have hcont : ContinuousAt x s :=
    hx.1.continuousOn.continuousAt ((maximalIntervalValue F s ξ).isOpen.mem_nhds hsI)
  have hdiscrepancy : Tendsto (fun j => ‖ξj j - x (sj j)‖) atTop (𝓝 0) := by
    have h := (hξj.sub (hcont.tendsto.comp hsj)).norm
    simpa only [Function.comp_apply, hxs, sub_self, norm_zero] using h
  have htimes : ∀ᶠ j in atTop, sj j ∈ Icc a b :=
    hsj.eventually (Icc_mem_nhds has hsb)
  obtain ⟨ρ, L, hρ, hL, hK, hKU, hlip, hpersist⟩ :=
    CommonInterval.common_interval F hF (maximalIntervalValue F s ξ) x hx
      a b (has.trans hsb).le hI
  have hT : 0 ≤ b-a := sub_nonneg.mpr (has.trans hsb).le
  have hevent (ε : ℝ) (hε : 0 < ε) : ∀ᶠ j in atTop,
      (Icc a b ⊆ (maximalIntervalValue (G j) (sj j) (ξj j)).carrier ∧
      classicalIVPOnValue (G j) (maximalIntervalValue (G j) (sj j) (ξj j))
        (solutionCurveValue (G j) (sj j) (ξj j)) (sj j) (ξj j)) ∧
      ∀ t ∈ Icc a b, ‖solutionCurveValue (G j) (sj j) (ξj j) t - x t‖ < ε := by
    let A := Real.exp (L * (b-a))
    let m := min (ρ/2) ε
    let δ := m / (2*A*(1+(b-a)))
    have hA : 0 < A := Real.exp_pos _
    have hm : 0 < m := lt_min (by positivity) hε
    have hden : 0 < 2*A*(1+(b-a)) := by positivity
    have hδ : 0 < δ := div_pos hm hden
    have hidentity : A * (δ + δ*(b-a)) = m/2 := by
      dsimp [δ]
      field_simp
    have hfield : ∀ᶠ j in atTop, ∀ q ∈ closedTube x a b ρ,
        ‖(G j).eval q.1 q.2 - F.eval q.1 q.2‖ ≤ δ := by
      have h := (Metric.tendstoUniformlyOn_iff.mp
        (hconv (closedTube x a b ρ) hK hKU)) δ hδ
      filter_upwards [h] with j hj q hq
      have hnorm : ‖(G j).eval q.1 q.2 - F.eval q.1 q.2‖ < δ := by
        simpa only [dist_eq_norm, norm_sub_rev] using hj q hq
      exact hnorm.le
    have hd : ∀ᶠ j in atTop, ‖ξj j - x (sj j)‖ < δ :=
      hdiscrepancy.eventually (Iio_mem_nhds hδ)
    filter_upwards [htimes, hfield, hd] with j htj hfj hdj
    have hsmall : A * (‖ξj j-x (sj j)‖ + δ*(b-a)) < m := by
      calc
        _ < A * (δ + δ*(b-a)) :=
          mul_lt_mul_of_pos_left (by linarith) hA
        _ = m/2 := hidentity
        _ < m := by linarith
    have hrho : A * (‖ξj j-x (sj j)‖ + δ*(b-a)) < ρ/2 :=
      hsmall.trans_le (min_le_left _ _)
    obtain ⟨hfull, hivp, _, hbound⟩ :=
      hpersist (G j) (hdom j) (hG j) δ hδ.le hfj (sj j) (ξj j) htj hrho
    refine ⟨⟨hfull, hivp⟩, ?_⟩
    intro t ht
    have hεsmall : Real.exp (L*(b-a)) * (‖ξj j-x (sj j)‖ + δ*(b-a)) <
        (2*ε)/2 := by
      have h := hsmall.trans_le (min_le_right _ _)
      dsimp [A] at h
      linarith
    exact (hbound t ht).1.trans_lt (by
      have h := CommonInterval.quantitative_bound (ρ := 2*ε) htj ht hL hδ.le
        (norm_nonneg _) hεsmall
      simpa only [Gronwall.E, mul_div_cancel_left₀ ε (by norm_num : (2:ℝ) ≠ 0)] using h)
  refine ⟨((hevent 1 (by norm_num)).mono fun _ h => h.1), ?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hevent ε hε] with j hj t ht
  simpa only [dist_eq_norm, norm_sub_rev] using hj.2 t ht

end D13Unified.Ch05.FieldConvergence
