import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Fejer
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.FejerConcentration
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.HeineCantor
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.ToIntervalMod

/-! Uniform Fejer convergence (K03.19.fejer, paper.tex:4958–4977).
The proof uses only proper componentwise Darboux integrals. Period reduction
and compactness give global regularity. Positivity, normalized kernel mass,
and the outside kernel bound give an error independent of the base point.
Expanding finite averages proves density, including real sine/cosine sums. -/
noncomputable section
namespace SingleVariableAnalysis
open Riemann Fourier
open scoped BigOperators

namespace Fourier

/-- Reduce both nearby arguments by the same integer period. Compact uniform
continuity then gives a radius independent of their position on the line. -/
theorem periodic_uniformContinuous {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) : UniformContinuous f := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (hf.continuousOn : ContinuousOn f (Set.Icc (-Real.pi-1) (Real.pi+1)))) ε hε
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro x y hxy
  have hdist : |x-y| < min δ 1 := by simpa only [Real.dist_eq] using hxy
  let k := toIcoDiv (show 0 < 2*Real.pi by positivity) (-Real.pi) x
  have hx := sub_toIcoDiv_zsmul_mem_Ico (show 0 < 2*Real.pi by positivity) (-Real.pi) x
  change -Real.pi ≤ x - k • (2*Real.pi) ∧
    x - k • (2*Real.pi) < -Real.pi + 2*Real.pi at hx
  have hd := abs_lt.mp (hdist.trans_le (min_le_right _ _))
  have hx' : x - k • (2*Real.pi) ∈ Set.Icc (-Real.pi-1) (Real.pi+1) := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : y - k • (2*Real.pi) ∈ Set.Icc (-Real.pi-1) (Real.pi+1) := by
    constructor <;> linarith [hx.1, hx.2, hd.1, hd.2]
  have hh : dist (x - k • (2*Real.pi)) (y - k • (2*Real.pi)) < δ := by
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using
      (hdist.trans_le (min_le_left _ _))
  simpa only [hp.sub_zsmul_eq] using hu _ hx' _ hy' hh

end Fourier

open Specs.SingleVariableAnalysis.Ch19.Fejer

theorem continuous_periodic_regularity : periodicRegularity := by
  intro f hf hp
  refine ⟨periodic_uniformContinuous hf hp, ?_,
    complexIntegrable_of_continuousOn (by linarith [Real.pi_pos]) hf.continuousOn⟩
  obtain ⟨M, hM, hb⟩ := (hp.isBounded_of_continuous
    (show 2*Real.pi ≠ 0 by positivity) hf).exists_pos_norm_le
  exact ⟨M, hM, fun x => hb _ (Set.mem_range_self x)⟩

namespace Fourier

/-- A real nonnegative kernel has norm equal to its real part. -/
theorem fejerKernel_norm (N : ℕ) (t : ℝ) :
    ‖fejerKernel N t‖ = (fejerKernel N t).re := by
  have he : fejerKernel N t = ((fejerKernel N t).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact fejerKernel_real N t
  calc
    _ = ‖((fejerKernel N t).re : ℂ)‖ := congrArg norm he
    _ = _ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fejerKernel_nonnegative N t)]

/-- The near-zero error and the uniform outside bound form a continuous
majorant on the entire reference interval; no indicator is integrated. -/
theorem fejer_error_bound (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f (2*Real.pi))
    (h : ∀ n : ℤ, ComplexIntegrable (fun y => f y * fourierMode (-n) y)
      (-Real.pi) Real.pi)
    {M η δ : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖f x‖ ≤ M)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (hu : ∀ x t : ℝ, |t| < δ → ‖f (x-t) - f x‖ ≤ η)
    (N : ℕ) (x : ℝ) :
    ‖fejerMean f h N x - f x‖ ≤
      η + 2*M / (((N : ℝ)+1) * Real.sin (δ/2)^2) := by
  let A : ℝ := 1 / (2*Real.pi)
  let B : ℝ := 1 / (((N : ℝ)+1) * Real.sin (δ/2)^2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have horder : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hfi := complexIntegrable_of_continuousOn horder hf.continuousOn
  obtain ⟨ht, hconv⟩ := fejerMean_convolution f ⟨hp, hfi⟩ h N x
  have hk := fejerKernel_integrable N
  obtain ⟨hc, hcv⟩ := complex_mul_value hk (-f x)
  obtain ⟨he, hev⟩ := complex_add_value ht hc
  let g : ℝ → ℂ := fun t => f (x-t)*fejerKernel N t + (-f x)*fejerKernel N t
  have he : ComplexIntegrable g (-Real.pi) Real.pi := he
  have herr : fejerMean f h N x - f x = (A : ℂ) * complexIntegral g he := by
    rw [hev, hcv, mul_add]
    have hn := fejerKernel_integral_mean N hk
    change (A : ℂ) * complexIntegral _ hk = 1 at hn
    rw [mul_left_comm (A : ℂ) (-f x), hn, mul_one, ← hconv]
    ring
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
      ‖g t‖ ≤ η * (fejerKernel N t).re + 2*M*B := by
    have hg : g t = (f (x-t) - f x) * fejerKernel N t := by dsimp [g]; ring
    rw [hg, norm_mul, fejerKernel_norm]
    by_cases hn : |t| < δ
    · exact (mul_le_mul_of_nonneg_right (hu x t hn)
        (fejerKernel_nonnegative N t)).trans (le_add_of_nonneg_right (by positivity))
    · have hout : (fejerKernel N t).re ≤ B :=
        (fejerKernel_outside_bound δ hδ hδπ N t (le_of_not_gt hn)
          (abs_le.mpr ⟨ht.1, ht.2⟩)).2
      have hd : ‖f (x-t) - f x‖ ≤ 2*M :=
        (norm_sub_le _ _).trans (by linarith [hb (x-t), hb x])
      exact (mul_le_mul hd hout (fejerKernel_nonnegative N t) (by positivity)).trans
        (le_add_of_nonneg_left (mul_nonneg hη (fejerKernel_nonnegative N t)))
  obtain ⟨hηk, hηkv⟩ := real_mul_value hk.1 η
  have hcB : RealIntegrable (fun _ : ℝ => 2*M*B) (-Real.pi) Real.pi :=
    realIntegrable_of_continuousOn horder continuous_const.continuousOn
  obtain ⟨hmaj, hmajv⟩ := real_add_value hηk hcB
  have hmono := realIntegral_mono _ _ he.norm hmaj hpoint
  have hnorm := (complex_norm_estimate g he).choose_spec.1
  have hcb := realIntegral_le_mul_bound hcB (fun _ _ => le_rfl)
  have hkn : A * realIntegral (fun t => (fejerKernel N t).re) hk.1 = 1 := by
    have hh := congrArg Complex.re (fejerKernel_integral_mean N hk)
    simpa [A, Complex.mul_re, complexIntegral,
      Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue] using hh
  change realIntegral _ he.norm ≤ realIntegral _ hmaj at hmono
  rw [hmajv, hηkv] at hmono
  rw [herr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
  calc
    _ ≤ A * (η * realIntegral _ hk.1 + realIntegral _ hcB) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hmono) hA
    _ ≤ A * (η * realIntegral _ hk.1 + (Real.pi - -Real.pi)*(2*M*B)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hcb) hA
    _ = η + 2*M / (((N : ℝ)+1) * Real.sin (δ/2)^2) := by
      have hlen : A * (Real.pi - -Real.pi) = 1 := by dsimp [A]; field_simp; ring
      calc
        _ = η * (A * realIntegral _ hk.1) + (A * (Real.pi - -Real.pi))*(2*M*B) := by ring
        _ = _ := by rw [hkn, hlen]; dsimp [B]; ring

end Fourier


theorem fejer_uniform_convergence : complexUniformConvergence := by
  intro f hf hp h ε hε
  obtain ⟨huc, ⟨M, hM, hb⟩, _⟩ := continuous_periodic_regularity f hf hp
  obtain ⟨d, hd, hu⟩ := Metric.uniformContinuous_iff.mp huc (ε/2) (half_pos hε)
  let δ := min (d/2) (Real.pi/2)
  have hδ : 0 < δ := lt_min (half_pos hd) (half_pos Real.pi_pos)
  have hδπ : δ < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hδd : δ < d := (min_le_left _ _).trans_lt (by linarith)
  have hnear (x t : ℝ) (ht : |t| < δ) : ‖f (x-t) - f x‖ ≤ ε/2 := by
    have hdist : dist (x-t) x < d := by
      simpa only [Real.dist_eq, sub_sub_cancel_left, abs_neg] using ht.trans hδd
    simpa only [dist_eq_norm] using (hu hdist).le
  have hlim : Filter.Tendsto (fun n : ℕ =>
      2*M / (((n : ℝ)+1)*Real.sin (δ/2)^2)) Filter.atTop (nhds 0) := by
    have hrec := (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) Filter.atTop (nhds (0 : ℝ)))
    have heq : (fun n : ℕ => 2*M / (((n : ℝ)+1)*Real.sin (δ/2)^2)) =
        (fun n : ℕ => 2*M * (1 / ((n : ℝ)+1) / Real.sin (δ/2)^2)) := by
      funext n; rw [div_mul_eq_div_div]; ring
    rw [heq]
    simpa only [zero_div, mul_zero] using
      (hrec.div_const (Real.sin (δ/2)^2)).const_mul (2*M)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (half_pos hε)
  refine ⟨N, fun n hn x => ?_⟩
  have ht : 2*M / (((n : ℝ)+1)*Real.sin (δ/2)^2) < ε/2 :=
    (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hN n hn)
  exact (fejer_error_bound f hf hp h hM.le hb (half_pos hε).le hδ hδπ hnear n x).trans_lt
    (by linarith)

theorem fejer_uniform_convergence_real : realUniformConvergence := by
  intro f hf hp
  exact fejer_uniform_convergence (fun x => (f x : ℂ))
    (Complex.continuous_ofReal.comp hf) (hp.comp Complex.ofReal)

/-- Expanding the two finite sums keeps every frequency inside [-N,N]. -/
theorem fejerMean_polynomial : meanPolynomial := by
  intro f h N
  classical
  let S : ℕ → Finset ℤ := fun k => Finset.Icc (-(k : ℤ)) (k : ℤ)
  let A : ℂ := ((1 / ((N : ℝ)+1) : ℝ) : ℂ)
  refine ⟨fun n => A * ∑ k ∈ Finset.range (N+1),
    if n ∈ S k then fourierCoeff f n (h n) else 0, fun x => ?_⟩
  change A * (∑ k ∈ Finset.range (N+1),
    ∑ n ∈ S k, fourierCoeff f n (h n) * fourierMode n x) = _
  have he (k : ℕ) (hk : k ∈ Finset.range (N+1)) :
      (∑ n ∈ S k, fourierCoeff f n (h n) * fourierMode n x) =
      ∑ n ∈ S N, (if n ∈ S k then fourierCoeff f n (h n) else 0) * fourierMode n x := by
    have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hsub : S k ⊆ S N := by
      intro n hn
      have hh := Finset.mem_Icc.mp hn
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    rw [← Finset.sum_subset hsub (fun n _ hn => by simp [hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [hn])
  rw [Finset.sum_congr rfl he, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [← Finset.sum_mul]
  ring

theorem trigonometric_polynomials_dense : complexDensity := by
  intro f hf hp ε hε
  have hi := (continuous_periodic_regularity f hf hp).2.2
  let h := fourierCoeff_integrable f hi
  obtain ⟨N, hN⟩ := fejer_uniform_convergence f hf hp h ε hε
  obtain ⟨c, hc⟩ := fejerMean_polynomial f h N
  exact ⟨N, c, fun x => (hc x) ▸ hN N le_rfl x⟩

theorem real_trigonometric_polynomials_dense : realDensity := by
  intro f hf hp ε hε
  obtain ⟨N, c, hc⟩ := trigonometric_polynomials_dense (fun x => (f x : ℂ))
    (Complex.continuous_ofReal.comp hf) (hp.comp Complex.ofReal) ε hε
  refine ⟨N, fun n => (c n).re, fun n => -(c n).im, fun x => ?_⟩
  have hre := (Complex.abs_re_le_norm
    ((∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c n * fourierMode n x) - (f x : ℂ))).trans_lt (hc x)
  have heq :
      (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((c n).re * Real.cos ((n : ℝ)*x) + (-(c n).im) * Real.sin ((n : ℝ)*x))) - f x =
      ((∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c n * fourierMode n x) - (f x : ℂ)).re := by
    rw [Complex.sub_re, Complex.ofReal_re, Complex.re_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [mode_euler]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add, sub_zero]
    ring
  rw [heq]
  exact hre

end SingleVariableAnalysis
