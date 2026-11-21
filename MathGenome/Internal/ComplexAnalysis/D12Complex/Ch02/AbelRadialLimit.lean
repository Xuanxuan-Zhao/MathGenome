import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.AbelRadialLimit
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Calculus.Deriv.Inv

open Filter
open scoped Topology

namespace D12Complex.AbelRadialLimit

/-- A convergent series has bounded terms, so a geometric majorant proves
absolute convergence after multiplying its nth term by t^n. -/
theorem absolute_convergence (a : ℕ → ℂ) (ζ S : ℂ) (_hζ : ζ ≠ 0)
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a n * ζ ^ n) atTop (𝓝 S))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n => ‖a n * ((t : ℂ) * ζ) ^ n‖) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq h.cauchySeq
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _
    ((summable_geometric_of_lt_one ht ht1).mul_left C)
  intro n
  simp only [mul_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht]
  calc
    ‖a n‖ * (t ^ n * ‖ζ‖ ^ n) = ‖a n * ζ ^ n‖ * t ^ n := by
      rw [norm_mul, norm_pow]; ring
    _ ≤ C * t ^ n := mul_le_mul_of_nonneg_right (hC n) (pow_nonneg ht n)

/-- Normalize the boundary terms b_n = a_n ζ^n and specialize complex Abel
to real parameters approaching one from below. -/
theorem radial_limit (a : ℕ → ℂ) (ζ S : ℂ) (_hζ : ζ ≠ 0)
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a n * ζ ^ n) atTop (𝓝 S)) :
    Tendsto (fun t : ℝ => ∑' n, a n * ((t : ℂ) * ζ) ^ n)
      (𝓝[Set.Ico 0 1] 1) (𝓝 S) := by
  have hA := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h
  rw [tendsto_map'_iff] at hA
  have hA' := hA.mono_left (nhdsWithin_mono (1 : ℝ) (show Set.Ico 0 1 ⊆ Set.Iio 1 from
    fun _ hx => hx.2))
  convert hA' using 1
  funext t
  apply tsum_congr
  intro n
  simp only [mul_pow]
  ring

theorem geometric_sum (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖z ^ n‖) ∧ HasSum (fun n : ℕ => z ^ n) (1 / (1 - z)) := by
  exact ⟨by simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg z) hz,
    by simpa only [one_div] using hasSum_geometric_of_norm_lt_one hz⟩

theorem geometric_holomorphic :
    HolomorphicOn (Metric.ball 0 1) (fun z : ℂ => ∑' n : ℕ, z ^ n) := by
  refine ⟨Metric.isOpen_ball, fun z hz => ?_⟩
  have hz' : ‖z‖ < 1 := by simpa using hz
  have hne : 1 - z ≠ 0 := by
    intro he
    have : z = 1 := by linear_combination -he
    simp [this] at hz'
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 / (1 - w)) z :=
    (differentiableAt_const (1 : ℂ)).div
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id) hne
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact (geometric_sum w (by simpa using hw)).2.tsum_eq

theorem geometric_boundary_divergence (z : ℂ) (hz : ‖z‖ = 1) :
    (¬ Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0)) ∧
    (¬ Summable (fun n : ℕ => z ^ n)) ∧
    (¬ ∃ S : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N, z ^ n) atTop (𝓝 S)) := by
  have hnot : ¬ Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0) := by
    intro h
    have hn : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
      simpa only [norm_pow, hz, one_pow, norm_zero] using h.norm
    have := tendsto_nhds_unique hn tendsto_const_nhds
    norm_num at this
  refine ⟨hnot, fun h => hnot h.tendsto_atTop_zero, ?_⟩
  rintro ⟨S, hS⟩
  apply hnot
  have ht := (hS.comp (tendsto_add_atTop_nat 1)).sub hS
  simpa only [Function.comp_apply, Finset.sum_range_succ, add_sub_cancel_left, sub_self]
    using ht

theorem geometric_no_finite_radial_limit :
    ¬ ∃ S : ℂ, Tendsto (fun t : ℝ => ∑' n : ℕ, (t : ℂ) ^ n)
      (𝓝[Set.Ico 0 1] 1) (𝓝 S) := by
  rintro ⟨S, hS⟩
  have hd : Tendsto (fun t : ℝ => (1 : ℂ) - (t : ℂ))
      (𝓝[Set.Ico 0 1] 1) (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 : ℂ))).sub
      (Complex.continuous_ofReal.tendsto (1 : ℝ))
    simpa using h.mono_left nhdsWithin_le_nhds
  have hm := hd.mul hS
  have heq : (fun t : ℝ => ((1 : ℂ) - (t : ℂ)) * ∑' n : ℕ, (t : ℂ) ^ n)
      =ᶠ[𝓝[Set.Ico 0 1] 1] (fun _ => (1 : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : ‖(t : ℂ)‖ < 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    rw [(geometric_sum (t : ℂ) ht').2.tsum_eq, one_div]
    apply mul_inv_cancel₀
    intro hn
    have hnorm : ‖(t : ℂ)‖ = 1 := by rw [← sub_eq_zero.mp hn]; norm_num
    linarith
  have hzero : Tendsto (fun _ : ℝ => (1 : ℂ)) (𝓝[Set.Ico 0 1] 1) (𝓝 0) := by
    simpa only [zero_mul] using hm.congr' heq
  have : NeBot (𝓝[Set.Ico (0 : ℝ) 1] 1) := by
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    infer_instance
  have := tendsto_nhds_unique hzero tendsto_const_nhds
  norm_num at this

end D12Complex.AbelRadialLimit
