import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ParameterDifferentiation
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Differentiating a parameter integral, paper.tex:2011–2041.
First take a countable pointwise limit of measurable difference quotients
to obtain actual measurability of the derivative section. The everywhere
quotient bound gives a Lipschitz bound, so the dominated parametric-integral
theorem applies. Neither step requires joint measurability or completion. -/

open Set Filter MeasureTheory
open scoped Topology
universe u
noncomputable section
namespace D11.Ch06.ParameterDifferentiation
open D11.Ch06.ScalarIntegral

/-- Derivative sections are measurable on the original measurable space. -/
theorem measurable_deriv_section {X : Type u} [MeasurableSpace X]
    {I : Set ℝ} {F : X → ℝ → ℝ} (hI : IsOpen I)
    (hm : ∀ t ∈ I, Measurable (fun x => F x t))
    (hd : ∀ x, DifferentiableOn ℝ (F x) I) {t : ℝ} (ht : t ∈ I) :
    Measurable (fun x => deriv (F x) t) := by
  classical
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (𝓝[≠] t)
  have huI : ∀ᶠ n in atTop, u n ∈ I :=
    (hu.mono_right nhdsWithin_le_nhds).eventually (hI.mem_nhds ht)
  let q : ℕ → X → ℝ := fun n x =>
    if u n ∈ I then (F x (u n) - F x t) / (u n - t) else 0
  have hqm : ∀ n, Measurable (q n) := by
    intro n
    by_cases hn : u n ∈ I
    · simpa only [q, ite_eq_left hn, Pi.sub_apply] using ((hm (u n) hn).sub (hm t ht)).div_const (u n - t)
    · simpa only [q, ite_eq_right hn] using (measurable_const : Measurable (fun _ : X => (0 : ℝ)))
  apply measurable_of_tendsto_metrizable hqm
  apply tendsto_pi_nhds.mpr
  intro x
  have hx : HasDerivAt (F x) (deriv (F x) t) t :=
    ((hd x t ht).differentiableAt (hI.mem_nhds ht)).hasDerivAt
  have hlim := hx.tendsto_slope.comp hu
  apply hlim.congr'
  filter_upwards [huI] with n hn
  simp only [q, ite_eq_left hn, Function.comp_apply, slope_def_field]

/-- The source's all-pairs quotient estimate is a Lipschitz estimate. -/
theorem lipschitzOnWith_of_quotient_bound {I : Set ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hb : ∀ s ∈ I, ∀ t ∈ I, s ≠ t → |(f t - f s) / (t - s)| ≤ c) :
    LipschitzOnWith (Real.nnabs c) f I := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  simp only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hc]
  by_cases hts : s = t
  · subst s
    simp
  · have hpos : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hts))
    have hb' := hb s hs t ht hts
    rw [abs_div, div_le_iff₀ hpos] at hb'
    exact hb'

theorem parameter_differentiation :
    Specs.D11.Ch06.ParameterDifferentiation.parameter_differentiation := by
  intro X _ μ I F g hI hF hd hg hg0 hb
  have hFm : ∀ t ∈ I, Measurable (fun x => F x t) := fun t ht => (hF t ht).1
  have hFi : ∀ t ∈ I, Integrable (fun x => F x t) μ :=
    fun t ht => ((scalarIntegrable_iff μ _).mp (hF t ht)).2
  have hgi : Integrable g μ := ((scalarIntegrable_iff μ _).mp hg).2
  have key : ∀ t ∈ I,
      scalarIntegrable μ (fun x => deriv (F x) t) ∧
      HasDerivAt (fun t => ∫ x, F x t ∂μ) (∫ x, deriv (F x) t ∂μ) t := by
    intro t ht
    have hdm := measurable_deriv_section hI hFm hd ht
    have hlip : ∀ᵐ x ∂μ, LipschitzOnWith (Real.nnabs (g x)) (F x) I :=
      Filter.Eventually.of_forall fun x => lipschitzOnWith_of_quotient_bound (hg0 x) (hb x)
    have hdiff : ∀ᵐ x ∂μ, HasDerivAt (F x) (deriv (F x) t) t :=
      Filter.Eventually.of_forall fun x =>
        ((hd x t ht).differentiableAt (hI.mem_nhds ht)).hasDerivAt
    have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x => F x s) μ := by
      filter_upwards [hI.mem_nhds ht] with s hs
      exact (hFm s hs).aestronglyMeasurable
    obtain ⟨hdi, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
      (hI.mem_nhds ht) hmeas (hFi t ht) hdm.aestronglyMeasurable hlip hgi hdiff
    exact ⟨(scalarIntegrable_iff μ _).mpr ⟨hdm, hdi⟩, hder⟩
  refine ⟨fun t ht => (key t ht).2.differentiableAt.differentiableWithinAt, ?_⟩
  intro t ht
  exact ⟨(key t ht).1, (key t ht).2, (key t ht).2.deriv⟩

end D11.Ch06.ParameterDifferentiation
