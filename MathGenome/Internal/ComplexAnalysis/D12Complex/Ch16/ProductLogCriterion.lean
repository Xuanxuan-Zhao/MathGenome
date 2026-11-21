import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.ProductLogCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.PrincipalLogarithm
import Mathlib.Analysis.SpecialFunctions.Log.Summable

noncomputable section
open Filter
open scoped Topology
namespace D12Complex.ProductLogCriterion

/-- Exponentiating an ordered finite logarithm sum gives its product. -/
lemma exp_sum_log (u : ℕ → ℂ) (hu : ∀ n, u n ≠ 0) (N n : ℕ) :
    Complex.exp (∑ k ∈ Finset.range n, PrincipalLog (u (k + N))) =
      ∏ k ∈ Finset.range n, u (k + N) := by
  change Complex.exp (∑ k ∈ Finset.range n, Complex.log (u (k + N))) = _
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl (fun k _ => Complex.exp_log (hu _))

/-- A convergent logarithm tail gives the full product, including its prefix. -/
lemma product_of_log_tail (u : ℕ → ℂ) (hu : ∀ n, u n ≠ 0)
    (N : ℕ) (S : ℂ)
    (hS : Tendsto (fun n => ∑ k ∈ Finset.range n, PrincipalLog (u (k + N)))
      atTop (𝓝 S)) :
    Tendsto (fun n => ∏ k ∈ Finset.range n, u k) atTop
      (𝓝 ((∏ k ∈ Finset.range N, u k) * Complex.exp S)) := by
  apply (tendsto_add_atTop_iff_nat N).mp
  have ht := (Complex.continuous_exp.continuousAt.tendsto.comp hS).const_mul
    (∏ k ∈ Finset.range N, u k)
  convert ht using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [Nat.add_comm n N, Finset.prod_range_add, exp_sum_log u hu]
  congr 1
  exact Finset.prod_congr rfl (fun k _ => by rw [Nat.add_comm])

/-- Ratios of successive nonzero partial products tend to one. -/
lemma factors_tendsto_one (u : ℕ → ℂ) (hu : ∀ n, u n ≠ 0)
    (P : ℂ) (hP : P ≠ 0)
    (ht : Tendsto (fun n => ∏ k ∈ Finset.range n, u k) atTop (𝓝 P)) :
    Tendsto u atTop (𝓝 1) := by
  have hr := (ht.comp (tendsto_add_atTop_nat 1)).div ht hP
  simp only [Function.comp_def, Finset.prod_range_succ] at hr
  have heq : (fun x => ((∏ k ∈ Finset.range x, u k) * u x) /
      (∏ k ∈ Finset.range x, u k)) = u := by
    funext n
    exact mul_div_cancel_left₀ _ (Finset.prod_ne_zero_iff.mpr (fun k _ => hu k))
  change Tendsto (fun x => ((∏ k ∈ Finset.range x, u k) * u x) /
      (∏ k ∈ Finset.range x, u k)) atTop (𝓝 (P / P)) at hr
  rwa [heq, div_self hP] at hr

/-- Every sequence approaching one eventually lies in the half disk. -/
lemma eventually_half_disk {u : ℕ → ℂ} (hu : Tendsto u atTop (𝓝 1)) :
    ∀ᶠ n in atTop, ‖u n - 1‖ < (1 / 2 : ℝ) := by
  have h := hu.eventually (Metric.ball_mem_nhds (x := (1 : ℂ)) (show (0 : ℝ) < 1 / 2 by norm_num))
  simpa only [Metric.mem_ball, dist_eq_norm] using h

/-- The logarithms of normalized partial products give a telescoping tail. -/
lemma log_tail_of_product (u : ℕ → ℂ) (hu : ∀ n, u n ≠ 0)
    (P : ℂ) (hP : P ≠ 0)
    (ht : Tendsto (fun n => ∏ k ∈ Finset.range n, u k) atTop (𝓝 P)) :
    ∃ N : ℕ, (∀ n, N ≤ n → ‖u n - 1‖ < (1 / 2 : ℝ)) ∧
      ∃ S : ℂ, Tendsto
        (fun n => ∑ k ∈ Finset.range n, PrincipalLog (u (k + N))) atTop (𝓝 S) := by
  let p : ℕ → ℂ := fun n => ∏ k ∈ Finset.range n, u k
  have hp : ∀ n, p n ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.mpr (fun k _ => hu k)
  let L : ℕ → ℂ := fun n => Complex.log (p n / P)
  have hratio : Tendsto (fun n => p n / P) atTop (𝓝 1) := by
    simpa only [div_self hP] using ht.div_const P
  have hL : Tendsto L atTop (𝓝 0) := by
    have hc := continuousAt_clog (show (1 : ℂ) ∈ Complex.slitPlane by simp)
    simpa only [L, Function.comp_def, Complex.log_one] using hc.tendsto.comp hratio
  have hd : Tendsto (fun n => L (n + 1) - L n) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using (hL.comp (tendsto_add_atTop_nat 1)).sub hL
  have hstrip : ∀ᶠ n in atTop,
      -Real.pi < (L (n + 1) - L n).im ∧ (L (n + 1) - L n).im ≤ Real.pi := by
    have hi := Complex.continuous_im.continuousAt.tendsto.comp hd
    have hmem : ∀ᶠ n in atTop, (L (n + 1) - L n).im ∈ Set.Ioo (-Real.pi) Real.pi := hi (Ioo_mem_nhds (show -Real.pi < (0 : ℂ).im by simpa using Real.pi_pos)
      (show (0 : ℂ).im < Real.pi by simpa using Real.pi_pos))
    exact hmem.mono (fun n hn => ⟨hn.1, hn.2.le⟩)
  have he : ∀ n, Complex.exp (L (n + 1) - L n) = u n := by
    intro n
    dsimp only [L]
    rw [Complex.exp_sub, Complex.exp_log (div_ne_zero (hp _) hP),
      Complex.exp_log (div_ne_zero (hp _) hP)]
    dsimp only [p]
    rw [Finset.prod_range_succ]
    field_simp [Finset.prod_ne_zero_iff.mpr (fun k _ => hu k)]
  have hlog : ∀ᶠ n in atTop, PrincipalLog (u n) = L (n + 1) - L n := by
    filter_upwards [hstrip] with n hn
    change Complex.log (u n) = _
    rw [← he n, Complex.log_exp hn.1 hn.2]
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlog.and (eventually_half_disk (factors_tendsto_one u hu P hP ht)))
  refine ⟨N, fun n hn => (hN n hn).2, -L N, ?_⟩
  have htel : ∀ n, (∑ k ∈ Finset.range n, PrincipalLog (u (k + N))) =
      L (n + N) - L N := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, (hN (n + N) (Nat.le_add_left N n)).1]
      rw [show n + 1 + N = (n + N) + 1 by omega]
      ring
  have htL := (hL.comp (tendsto_add_atTop_nat N)).sub_const (L N)
  simpa only [htel, Function.comp_apply, zero_sub] using htL

theorem product_log_criterion :
    Specs.D12Complex.Ch16.ProductLogCriterion.product_log_criterion_type := by
  intro u hu
  constructor
  · rintro ⟨P, hP, ht⟩
    obtain ⟨N, _, S, hS⟩ := log_tail_of_product u hu P hP ht
    exact ⟨factors_tendsto_one u hu P hP ht, N, S, hS⟩
  · rintro ⟨_, N, S, hS⟩
    exact ⟨_, mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k _ => hu k))
      (Complex.exp_ne_zero S), product_of_log_tail u hu N S hS⟩

theorem product_nonzero_of_summable_norm :
    Specs.D12Complex.Ch16.ProductLogCriterion.product_nonzero_of_summable_norm_type := by
  intro u hu hs
  have hc : Summable (fun n => u n - 1) := hs.of_norm
  have hl : Summable (fun n => Complex.log (u n)) := by
    exact (Complex.summable_log_one_add_of_summable hc).congr
      (fun n => congrArg Complex.log (by ring))
  have hlim := (Complex.hasProd_of_hasSum_log hu hl.hasSum).tendsto_prod_nat
  exact ⟨_, Complex.exp_ne_zero _, hlim⟩

end D12Complex.ProductLogCriterion
