import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Convergence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.LocalConvergence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.MeanInequality
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace SingleVariableAnalysis
open Set Filter Riemann Riemann.Improper Fourier
open scoped Topology
open Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Convergence
namespace FourierPiecewiseC1

/-- Pass a derivative bound to the finite right-hand limiting value.
The actual endpoint value is never used. -/
theorem right_limit_estimate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x r M : ℝ} {L : E}
    (hd : ∀ y ∈ Ioo x (x+r), DifferentiableAt ℝ f y)
    (hb : ∀ y ∈ Ioo x (x+r), ‖deriv f y‖ ≤ M)
    (hL : Tendsto f (𝓝[>] x) (𝓝 L)) {t : ℝ} (ht : 0 < t) (htr : t < r) :
    ‖f (x+t)-L‖ ≤ M*t := by
  have hy : x+t ∈ Ioo x (x+r) := ⟨by linarith, by linarith⟩
  have hev : ∀ᶠ y in 𝓝[>] x, y ∈ Ioo x (x+r) := by
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds (show x < x+r by linarith)))] with y h1 h2
    exact ⟨h1, h2⟩
  have hn : Tendsto (fun y => ‖f (x+t)-f y‖) (𝓝[>] x)
      (𝓝 ‖f (x+t)-L‖) := (tendsto_const_nhds.sub hL).norm
  have hr : Tendsto (fun y : ℝ => M*‖x+t-y‖) (𝓝[>] x)
      (𝓝 (M*‖x+t-x‖)) :=
    (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)).norm.const_mul M
  have H := le_of_tendsto_of_tendsto hn hr (hev.mono fun y hy' =>
    Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Ioo _ _) hy' hy)
  simpa only [sub_self, add_sub_cancel_left, Real.norm_eq_abs, abs_of_pos ht] using H

/-- The corresponding left estimate uses the same open-cell mean inequality. -/
theorem left_limit_estimate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x r M : ℝ} {L : E}
    (hd : ∀ y ∈ Ioo (x-r) x, DifferentiableAt ℝ f y)
    (hb : ∀ y ∈ Ioo (x-r) x, ‖deriv f y‖ ≤ M)
    (hL : Tendsto f (𝓝[<] x) (𝓝 L)) {t : ℝ} (ht : 0 < t) (htr : t < r) :
    ‖f (x-t)-L‖ ≤ M*t := by
  have hy : x-t ∈ Ioo (x-r) x := ⟨by linarith, by linarith⟩
  have hev : ∀ᶠ y in 𝓝[<] x, y ∈ Ioo (x-r) x := by
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Ioi_mem_nhds (show x-r < x by linarith)))] with y h1 h2
    exact ⟨h2, h1⟩
  have hn : Tendsto (fun y => ‖f (x-t)-f y‖) (𝓝[<] x)
      (𝓝 ‖f (x-t)-L‖) := (tendsto_const_nhds.sub hL).norm
  have hr : Tendsto (fun y : ℝ => M*‖x-t-y‖) (𝓝[<] x)
      (𝓝 (M*‖x-t-x‖)) :=
    (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)).norm.const_mul M
  have H := le_of_tendsto_of_tendsto hn hr (hev.mono fun y hy' =>
    Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Ioo _ _) hy' hy)
  simpa only [show x-t-x = -t by ring, norm_neg, Real.norm_eq_abs, abs_of_pos ht] using H


/-- A bounded proper-on-truncations function has a convergent finite left
improper integral. This uses the Darboux integral Cauchy criterion. -/
theorem left_converges_of_bounded {g : ℝ → ℝ} {b B : ℝ}
    (hb : 0 < b) (hB : 0 < B)
    (hg : ∀ u : ℝ, 0 < u → u ≤ b → RealIntegrable g u b)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ b → |g t| ≤ B) :
    LeftConverges .real g (0 : WithBot ℝ) b := by
  have hreg : LeftRegular .real g (0 : WithBot ℝ) b :=
    ⟨WithBot.coe_lt_coe.mpr hb, fun t =>
      hg t.val (WithBot.coe_lt_coe.mp t.property.1) t.property.2.le⟩
  apply (left_cauchy_criterion .real g (0 : WithBot ℝ) b hreg).mpr
  intro ε hε
  obtain ⟨r, hr0, hr⟩ := exists_between (lt_min hb (div_pos hε hB))
  refine ⟨⟨r, WithBot.coe_lt_coe.mpr hr0, (lt_min_iff.mp hr).1⟩,
    fun u v huv hvr => ?_⟩
  have hgi := (hg u.val (WithBot.coe_lt_coe.mp u.property.1)
    u.property.2.le).subinterval le_rfl huv.le v.property.2.le
  obtain ⟨hn, hnorm, _⟩ := real_norm_estimate g hgi
  have hbn : realIntegral _ hn ≤ (v.val-u.val)*B := by
    apply realIntegral_le_mul_bound hn
    intro t ht
    exact hbound t ((WithBot.coe_lt_coe.mp u.property.1).trans_le ht.1)
      (ht.2.trans v.property.2.le)
  refine ⟨hgi, hnorm.trans hbn |>.trans_lt ?_⟩
  have hu := WithBot.coe_lt_coe.mp u.property.1
  have hv : v.val < ε / B := hvr.trans (lt_min_iff.mp hr).2
  exact (mul_lt_mul_of_pos_right (by linarith : v.val-u.val < ε/B) hB).trans_eq
    (div_mul_cancel₀ ε hB.ne')

/-- The Dini numerator is O(t), by adding the two one-sided estimates. -/
theorem density_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x r Mm Mp : ℝ} {Lm Lp : E}
    (hm : sideC1Bound f (x-r) x Mm) (hp : sideC1Bound f x (x+r) Mp)
    (hl : Tendsto f (𝓝[<] x) (𝓝 Lm)) (hr : Tendsto f (𝓝[>] x) (𝓝 Lp))
    {t : ℝ} (ht : 0 < t) (htr : t < r) :
    ‖f (x+t)+f (x-t)-Lp-Lm‖ / t ≤ Mm+Mp := by
  have h1 := right_limit_estimate hp.1 hp.2.2 hr ht htr
  have h2 := left_limit_estimate hm.1 hm.2.2 hl ht htr
  apply (div_le_iff₀ ht).mpr
  calc
    ‖f (x+t)+f (x-t)-Lp-Lm‖ = ‖(f (x+t)-Lp)+(f (x-t)-Lm)‖ := by
      congr 1; abel
    _ ≤ ‖f (x+t)-Lp‖ + ‖f (x-t)-Lm‖ := norm_add_le _ _
    _ ≤ (Mm+Mp)*t := by linarith

/-- All positive truncations are proper Riemann integrals, since the
functions are continuous strictly inside the two cells. -/
theorem density_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x r Mm Mp : ℝ} (Lm Lp : E)
    (hm : sideC1Bound f (x-r) x Mm) (hp : sideC1Bound f x (x+r) Mp)
    {u v : ℝ} (hu : 0 < u) (hv : v < r) :
    ContinuousOn (fun t => ‖f (x+t)+f (x-t)-Lp-Lm‖ / t) (Icc u v) := by
  intro t ht
  have ht0 : 0 < t := hu.trans_le ht.1
  have htr : t < r := ht.2.trans_lt hv
  have hcp : ContinuousAt (fun t => f (x+t)) t :=
    (hp.1 (x+t) ⟨by linarith, by linarith⟩).continuousAt.comp
      (continuousAt_const.add continuousAt_id)
  have hcm : ContinuousAt (fun t => f (x-t)) t :=
    (hm.1 (x-t) ⟨by linarith, by linarith⟩).continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  exact ((((hcp.add hcm).sub continuousAt_const).sub continuousAt_const).norm.div
    continuousAt_id ht0.ne').continuousWithinAt

/-- Boundedness and proper truncation integrability establish the full
independent-endpoint improper Dini integral. -/
theorem dini_condition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (x : ℝ) (Lm Lp : E) (hc : localPiecewiseC1 f x)
    (hl : Tendsto f (𝓝[<] x) (𝓝 Lm)) (hr : Tendsto f (𝓝[>] x) (𝓝 Lp)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi ∧
      Converges .real (fun t => ‖f (x+t)+f (x-t)-Lp-Lm‖ / t)
        (0 : WithBot ℝ) (δ : WithTop ℝ) := by
  obtain ⟨r, hr0, Mm, Mp, hMm, hMp, hm, hp⟩ := hc
  obtain ⟨δ, hδ, hδmin⟩ := exists_between (lt_min hr0 Real.pi_pos)
  have hδr := (lt_min_iff.mp hδmin).1
  have hδπ := (lt_min_iff.mp hδmin).2
  let g : ℝ → ℝ := fun t => ‖f (x+t)+f (x-t)-Lp-Lm‖ / t
  have hg {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ δ) :
      RealIntegrable g u v :=
    realIntegrable_of_continuousOn huv (density_continuousOn Lm Lp hm hp hu (hv.trans_lt hδr))
  have hbound (t : ℝ) (ht : 0 < t) (htδ : t ≤ δ) : |g t| ≤ Mm+Mp+1 := by
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) ht.le)]
    exact (density_bound hm hp hl hr ht (htδ.trans_lt hδr)).trans (by linarith)
  let c : RegularPoint (0 : WithBot ℝ) (δ : WithTop ℝ) :=
    ⟨δ/2, WithBot.coe_lt_coe.mpr (by linarith), WithTop.coe_lt_coe.mpr (by linarith)⟩
  have hleft : LeftConverges .real g (0 : WithBot ℝ) (δ/2) :=
    left_converges_of_bounded (by linarith) (by linarith : 0 < Mm+Mp+1)
      (fun u hu hub => hg hu hub (by linarith))
      (fun t ht htb => hbound t ht (by linarith))
  have hright := FourierDini.rightConverges_real_of_proper (by linarith : δ/2 < δ)
    (hg (by linarith : 0 < δ/2) (by linarith) le_rfl)
  obtain ⟨l, hl'⟩ := hleft
  obtain ⟨s, hs'⟩ := hright
  refine ⟨δ, hδ, hδπ, l+s, ?_, c, l, s, hl', hs', rfl⟩
  intro u v hu huv hv
  exact hg (WithBot.coe_lt_coe.mp hu) huv (WithTop.coe_lt_coe.mp hv).le

end FourierPiecewiseC1

/-- Complex Dini condition, obtained from the stated local C¹ hypotheses. -/
theorem fourier_piecewiseC1_dini : complexDiniCondition := by
  intro f x Lm Lp hc hl hr
  exact FourierPiecewiseC1.dini_condition f x Lm Lp hc hl hr

/-- Real Dini condition with the ordinary absolute-value numerator. -/
theorem fourier_piecewiseC1_real_dini : realDiniCondition := by
  intro f x Lm Lp hc hl hr
  simpa only [Real.norm_eq_abs] using FourierPiecewiseC1.dini_condition f x Lm Lp hc hl hr

/-- Piecewise C¹ Fourier convergence holds at every real x, including seams,
without imposing either one-sided limiting value on the assigned jump value. -/
theorem fourier_piecewiseC1_convergence : complexConvergence := by
  intro f hf h x Lm Lp hc hl hr
  obtain ⟨δ, hδ, hδπ, hd⟩ := fourier_piecewiseC1_dini f x Lm Lp hc hl hr
  exact fourier_dini_local_convergence f hf h x Lm Lp δ hδ hδπ hl hr hd

/-- The real scalar specialization, using the same canonical partial sums. -/
theorem fourier_piecewiseC1_real_convergence : realConvergence := by
  intro f hf h x Lm Lp hc hl hr
  obtain ⟨δ, hδ, hδπ, hd⟩ := fourier_piecewiseC1_real_dini f x Lm Lp hc hl hr
  exact fourier_dini_real_local_convergence f hf h x Lm Lp δ hδ hδπ hl hr hd

end SingleVariableAnalysis
