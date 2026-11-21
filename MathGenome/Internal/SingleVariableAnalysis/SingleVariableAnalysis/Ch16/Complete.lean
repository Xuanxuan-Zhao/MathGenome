import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.SupSpace
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Continuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Complete

/-!
Completeness of the real and complex sup-norm spaces (K03.16.complete).

The canonical norm bounds every pointwise difference. Thus a norm Cauchy
sequence is uniformly Cauchy, and the upstream uniform Cauchy criterion
constructs a scalar-valued uniform limit. The upstream uniform-limit theorem
proves its continuity; packaging that function as a continuous map and using
the sup-norm/uniform-convergence bridge proves convergence in norm.
This argument never chooses a point of K and includes the empty compact set.
-/

namespace SingleVariableAnalysis

open scoped Topology

theorem realSupSpace_complete (K : Set ℝ) [CompactSpace K]
    (F : ℕ → C(K, ℝ))
    (hF : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, ‖F n - F m‖ < ε) :
    ∃ f : C(K, ℝ),
      Filter.Tendsto (fun n => ‖F n - f‖) Filter.atTop (𝓝 0) := by
  have hU : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, ∀ x : K, |F n x - F m x| < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hF ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn x
    have hx := ((F n - F m).norm_coe_le_norm x).trans_lt (hN m hm n hn)
    simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using hx
  obtain ⟨u, hu⟩ := (real_uniform_cauchy_criterion (fun n x => F n x)).mpr hU
  let f : C(K, ℝ) := ⟨u, realUniformLimit_continuous (fun n x => F n x) u
    (fun n => (F n).continuous) hu⟩
  exact ⟨f, (realSupSpace_norm_converges_iff_uniform K F f).mpr hu⟩

theorem complexSupSpace_complete (K : Set ℝ) [CompactSpace K]
    (F : ℕ → C(K, ℂ))
    (hF : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, ‖F n - F m‖ < ε) :
    ∃ f : C(K, ℂ),
      Filter.Tendsto (fun n => ‖F n - f‖) Filter.atTop (𝓝 0) := by
  have hU : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, ∀ x : K, ‖F n x - F m x‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hF ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn x
    exact ((F n - F m).norm_coe_le_norm x).trans_lt (hN m hm n hn)
  obtain ⟨u, hu⟩ := (complex_uniform_cauchy_criterion (fun n x => F n x)).mpr hU
  let f : C(K, ℂ) := ⟨u, complexUniformLimit_continuous (fun n x => F n x) u
    (fun n => (F n).continuous) hu⟩
  exact ⟨f, (complexSupSpace_norm_converges_iff_uniform K F f).mpr hu⟩

theorem realSupSpace_cauchySeq_converges (K : Set ℝ) [CompactSpace K]
    (F : ℕ → C(K, ℝ)) (hF : CauchySeq F) :
    ∃ f : C(K, ℝ), Filter.Tendsto F Filter.atTop (𝓝 f) := by
  obtain ⟨f, hf⟩ := realSupSpace_complete K F (by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hF ε hε
    exact ⟨N, fun m hm n hn => by
      simpa only [dist_eq_norm] using hN n hn m hm⟩)
  exact ⟨f, tendsto_iff_norm_sub_tendsto_zero.mpr hf⟩

theorem complexSupSpace_cauchySeq_converges (K : Set ℝ) [CompactSpace K]
    (F : ℕ → C(K, ℂ)) (hF : CauchySeq F) :
    ∃ f : C(K, ℂ), Filter.Tendsto F Filter.atTop (𝓝 f) := by
  obtain ⟨f, hf⟩ := complexSupSpace_complete K F (by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hF ε hε
    exact ⟨N, fun m hm n hn => by
      simpa only [dist_eq_norm] using hN n hn m hm⟩)
  exact ⟨f, tendsto_iff_norm_sub_tendsto_zero.mpr hf⟩

end SingleVariableAnalysis
