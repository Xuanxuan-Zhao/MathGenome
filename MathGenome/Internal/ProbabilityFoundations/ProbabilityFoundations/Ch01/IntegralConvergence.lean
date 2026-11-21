import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.IntegralConvergence

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ProbabilityFoundations.Ch01

/-- Monotone convergence, including monotonicity of the extended integrals. -/
theorem monotone_convergence : Specs.MonotoneConvergence := by
  intro α m μ F f hF _hf hmono hlim
  exact ⟨fun i j hij => lintegral_mono_ae (hmono.mono fun x hx => hx hij),
    lintegral_tendsto_of_tendsto_of_monotone (fun n => (hF n).aemeasurable) hmono hlim⟩

/-- Fatou's inequality with possibly infinite integrals. -/
theorem fatou : Specs.Fatou := by
  intro α m μ F hF
  exact lintegral_liminf_le hF

/-- Dominated convergence in L¹, for real, complex, and separable normed codomains. -/
theorem dominated_convergence : Specs.DominatedConvergence := by
  intro α m μ E nE rE mE bE sE F f g hF hf _hg _hpos hgint hbound hlim
  have hfbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x := by
    filter_upwards [ae_all_iff.mpr hbound, hlim] with x hx hconv
    exact le_of_tendsto' hconv.norm hx
  have hfint : Integrable f μ := hgint.mono' hf.stronglyMeasurable.aestronglyMeasurable hfbound
  have hFint : ∀ n, Integrable (F n) μ := fun n =>
    hgint.mono' (hF n).stronglyMeasurable.aestronglyMeasurable (hbound n)
  refine ⟨hfint, hFint, ?_, ?_⟩
  swap
  · exact tendsto_integral_of_dominated_convergence g
      (fun n => (hFint n).aestronglyMeasurable) hgint hbound hlim
  have hconv := tendsto_integral_of_dominated_convergence
    (F := fun n x => ‖F n x - f x‖) (f := fun _ => (0 : ℝ))
    (fun x => g x + g x)
    (fun n => ((hFint n).sub hfint).norm.aestronglyMeasurable)
    (hgint.add hgint) ?_ ?_
  · simpa using hconv
  · intro n
    filter_upwards [hbound n, hfbound] with x hx hfx
    simpa only [Real.norm_eq_abs, abs_norm] using
      (norm_sub_le (F n x) (f x)).trans (add_le_add hx hfx)
  · filter_upwards [hlim] with x hx
    simpa using (hx.sub_const (f x)).norm

/-- Bounded convergence on a finite-measure support in an arbitrary measure space. -/
theorem bounded_convergence : Specs.BoundedConvergence := by
  intro α m μ E nE rE mE bE sE F f s C hs hfinite hC hF hf hbound hzero hlim
  let g : α → ℝ := s.indicator (fun _ => C)
  have hg : Measurable g := measurable_const.indicator hs
  have hgnonneg : ∀ᵐ x ∂μ, 0 ≤ g x := by
    exact ae_of_all μ (fun x => Set.indicator_nonneg (fun _ _ => hC) x)
  have hgint : Integrable g μ :=
    (integrable_indicator_iff hs).mpr (integrableOn_const hfinite.ne)
  have hdom : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x := by
    intro n
    filter_upwards [hbound n, hzero n] with x hx hzx
    by_cases hxs : x ∈ s
    · simpa [g, hxs] using hx hxs
    · simp [g, hxs, hzx hxs]
  exact dominated_convergence μ F f g hF hf hg hgnonneg hgint hdom hlim

end ProbabilityFoundations.Ch01
