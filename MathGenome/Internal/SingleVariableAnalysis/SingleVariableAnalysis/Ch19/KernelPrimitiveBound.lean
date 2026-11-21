import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.KernelPrimitiveBound
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.DirichletKernel
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.MonotoneSubstitution
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
The uniform primitive estimate used by Dirichlet–Jordan (K03.19.jordan).
The integral throughout is the shared proper Darboux integral. Integration by
parts bounds sinc above 1; its continuous extension controls the interval near
zero. Jordan's sine inequality and the cubic Taylor bound control the correction
term. Scaling and the finite kernel identity then give the explicit common bound
`8 + π³`, including singleton intervals and intervals starting at zero.
-/
noncomputable section
namespace SingleVariableAnalysis.Fourier
open Set Filter Riemann
open scoped Topology
open Specs.SingleVariableAnalysis.Ch19.KernelPrimitiveBound

/-- The proper Darboux integral of a continuous real function on an ordered interval. -/
theorem continuous_integrable {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : RealIntegrable f a b :=
  realIntegrable_of_continuousOn hab hf

/-- Norm domination for the proper integral, with a possibly nonconstant majorant. -/
theorem integral_abs_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b)
    (h : ∀ x ∈ Icc a b, |f x| ≤ g x) :
    |realIntegral f hf| ≤ realIntegral g hg := by
  simpa only [Real.norm_eq_abs] using (real_norm_estimate f hf).choose_spec.1.trans
    (realIntegral_mono _ _ hf.norm hg (by simpa only [Real.norm_eq_abs] using h))

theorem sinc_integrable {u v : ℝ} (huv : u ≤ v) :
    RealIntegrable Real.sinc u v :=
  continuous_integrable huv Real.continuous_sinc.continuousOn

/-- The nonsingular part is bounded even when an endpoint is zero. -/
theorem sinc_small_bound {u v : ℝ} (hu : 0 ≤ u) (_huv : u ≤ v) (hv : v ≤ 1)
    (h : RealIntegrable Real.sinc u v) : |realIntegral Real.sinc h| ≤ 1 := by
  have hn := (real_norm_estimate Real.sinc h).choose
  have he := (real_norm_estimate Real.sinc h).choose_spec.1
  change |realIntegral Real.sinc h| ≤ _ at he
  have hb := realIntegral_le_mul_bound hn (M := 1)
    (fun x _ => by simpa only [Real.norm_eq_abs] using Real.abs_sinc_le_one x)
  simp only [mul_one] at hb
  exact he.trans (hb.trans (by linarith))

/-- Equality on the open integration interval suffices; endpoint values have
zero contribution to a proper Darboux integral. -/
theorem integral_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b)
    (he : ∀ x ∈ Ioo a b, f x = g x) : realIntegral f hf = realIntegral g hg := by
  obtain ⟨hg', hh⟩ := real_endpoint_extensions f g a b he hf
  exact hh.symm

/-- Above 1, integration by parts reduces the oscillation to an integrable
inverse-square majorant. -/
theorem sinc_tail_bound {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v)
    (h : RealIntegrable Real.sinc u v) : |realIntegral Real.sinc h| ≤ 3 := by
  have hpos : ∀ x ∈ Icc u v, 0 < x := fun x hx => by linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc u v) :=
    continuousOn_id.inv₀ (fun x hx => (hpos x hx).ne')
  have hc2 : ContinuousOn (fun x : ℝ => -(1 / x^2)) (Icc u v) := by
    intro x hx
    exact (continuousWithinAt_const.div (continuousWithinAt_id.pow 2)
      (pow_ne_zero 2 (hpos x hx).ne')).neg
  have hi := continuous_integrable huv hc2
  obtain ⟨h₁, h₂, he⟩ := real_parts (fun x : ℝ => x⁻¹) (fun x => -Real.cos x)
    (fun x => -(1 / x^2)) Real.sin u v huv hc Real.continuous_cos.neg.continuousOn
    (fun x hx => by simpa only [one_div] using hasDerivAt_inv (hpos x (Ioo_subset_Icc_self hx)).ne')
    (fun x _ => by convert (Real.hasDerivAt_cos x).neg using 1; simp)
    hi (continuous_integrable huv Real.continuous_sin.continuousOn)
  have hmain : realIntegral _ h₁ = realIntegral Real.sinc h := by
    apply integral_congr h₁ h
    intro x hx
    rw [Real.sinc_of_ne_zero (hpos x (Ioo_subset_Icc_self hx)).ne']
    ring
  have hp : RealIntegrable (fun x : ℝ => x⁻¹^2) u v := continuous_integrable huv (hc.pow 2)
  have hpow : realIntegral (fun x : ℝ => x⁻¹^2) hp = u⁻¹ - v⁻¹ := by
    have heq := real_ftc_second (fun x : ℝ => -x⁻¹) (fun x => x⁻¹^2)
      u v huv hc.neg (fun x hx => ?_) hp
    · simpa only [neg_sub_neg] using heq
    · convert (hasDerivAt_inv (hpos x (Ioo_subset_Icc_self hx)).ne').neg using 1; field_simp
  have hrem : |realIntegral _ h₂| ≤ u⁻¹ - v⁻¹ := by
    rw [← hpow]
    apply integral_abs_le h₂ hp
    intro x hx
    simp only [neg_mul_neg, one_div, inv_pow, abs_mul, abs_pow,
      abs_inv, abs_of_pos (hpos x hx)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr (sq_nonneg x)) (Real.abs_cos_le_one x)
  have hbu : |u⁻¹ * -Real.cos u| ≤ u⁻¹ := by
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos (hpos u ⟨le_rfl, huv⟩)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr (by linarith)) (Real.abs_cos_le_one u)
  have hbv : |v⁻¹ * -Real.cos v| ≤ v⁻¹ := by
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos (hpos v ⟨huv, le_rfl⟩)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr (by linarith)) (Real.abs_cos_le_one v)
  change realIntegral _ h₁ = _ - _ - realIntegral _ h₂ at he
  rw [hmain] at he
  rw [he]
  calc
    _ ≤ |v⁻¹ * -Real.cos v - u⁻¹ * -Real.cos u| + |realIntegral _ h₂| := abs_sub _ _
    _ ≤ (|v⁻¹ * -Real.cos v| + |u⁻¹ * -Real.cos u|) + |realIntegral _ h₂| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (u⁻¹ + v⁻¹) + (u⁻¹ - v⁻¹) := by linarith
    _ ≤ 3 := by have := inv_le_one_of_one_le₀ hu; linarith


/-- Uniform cancellation for sinc on every nonnegative finite interval. -/
theorem sinc_bound {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (h : RealIntegrable Real.sinc u v) : |realIntegral Real.sinc h| ≤ 4 := by
  by_cases hv : v ≤ 1
  · exact (sinc_small_bound hu huv hv h).trans (by norm_num)
  by_cases hu' : 1 ≤ u
  · exact (sinc_tail_bound hu' huv h).trans (by norm_num)
  have hu1 : u ≤ 1 := le_of_not_ge hu'
  have h1v : 1 ≤ v := le_of_not_ge hv
  have hl := sinc_integrable hu1
  have hr := sinc_integrable h1v
  have he := (real_split Real.sinc hu1 h1v h.bounded).2 h hl hr
  change realIntegral Real.sinc h = realIntegral _ hl + realIntegral _ hr at he
  rw [he]
  have hb := (abs_add_le _ _).trans (add_le_add
    (sinc_small_bound hu hu1 le_rfl hl) (sinc_tail_bound le_rfl h1v hr))
  norm_num at hb ⊢
  exact hb

theorem sinc_integral_bound : sincIntegralBound := by
  refine ⟨4, by norm_num, fun u v hu huv => ⟨sinc_integrable huv, ?_⟩⟩
  exact sinc_bound hu huv _

/-- Scaling preserves the uniform sinc cancellation bound, uniformly in frequency. -/
theorem scaled_sinc_bound {ν u v : ℝ} (hν : 0 < ν) (hu : 0 ≤ u) (huv : u ≤ v) :
    ∃ h : RealIntegrable (fun t => ν * Real.sinc (ν*t)) u v,
      |realIntegral _ h| ≤ 4 := by
  have hscale : ν * u ≤ ν * v := mul_le_mul_of_nonneg_left huv hν.le
  have hs := sinc_integrable hscale
  have ho : OrientedRealIntegrable Real.sinc (ν*u) (ν*v) := by
    simpa only [OrientedRealIntegrable, Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue,
      min_eq_left hscale, max_eq_right hscale] using hs
  obtain ⟨h, he⟩ := real_monotone_substitution (fun t => ν*t) (fun _ => ν)
    Real.sinc huv ⟨continuousOn_const, fun t _ => by
      simpa using ((hasDerivAt_id t).const_mul ν).hasDerivWithinAt⟩
    (Or.inl (fun x _ y _ hxy => mul_le_mul_of_nonneg_left hxy hν.le)) ho
  refine ⟨h, ?_⟩
  change realIntegral _ h = orientedRealIntegral Real.sinc ho at he
  rw [he]
  have heq : orientedRealIntegral Real.sinc ho = realIntegral Real.sinc hs :=
    oriented_real_agreement Real.sinc hscale ho hs
  rw [heq]
  exact sinc_bound (mul_nonneg hν.le hu) hscale hs
/-- Continuous correction term for the sine quotient. -/
theorem correction_bound {t : ℝ} (ht : 0 ≤ t) (hp : t ≤ Real.pi) :
    |correction t| ≤ Real.pi * t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [correction]
  have hs : 0 < Real.sin (t/2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith [Real.pi_pos])
  have hlow := Real.mul_le_sin (show 0 ≤ t/2 by linarith)
    (show t/2 ≤ Real.pi/2 by linarith)
  have htay := Real.abs_sub_sin_le (t/2)
  rw [abs_of_pos (by linarith : 0 < t/2)] at htay
  have he : correction t = (t/2 - Real.sin (t/2)) / (Real.sin (t/2) * (t/2)) := by
    unfold correction
    field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hs (by linarith))]
  apply (div_le_iff₀ (mul_pos hs (by linarith))).mpr
  apply htay.trans
  have hh : t ≤ Real.pi * Real.sin (t/2) := by
    have := (div_le_iff₀ Real.pi_pos).mp
      (show t / Real.pi ≤ Real.sin (t/2) by convert hlow using 1; ring)
    linarith
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hh), sq_nonneg t]

theorem correction_neg (t : ℝ) : correction (-t) = -correction t := by
  simp [correction, Real.sin_neg, neg_div, div_neg, neg_sub]
  ring
theorem correction_abs_bound {t : ℝ} (ht : |t| ≤ Real.pi) : |correction t| ≤ Real.pi * |t| := by
  by_cases h : 0 ≤ t
  · simpa only [abs_of_nonneg h] using correction_bound h ((le_abs_self t).trans ht)
  · have hn : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge h)
    have he := correction_bound hn (by simpa only [abs_of_nonpos (le_of_not_ge h)] using ht)
    simpa only [correction_neg, abs_neg, abs_of_nonpos (le_of_not_ge h)] using he
theorem correction_at_zero : correctionAtZero := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min Real.pi (ε/Real.pi), lt_min Real.pi_pos (div_pos hε Real.pi_pos), ?_⟩
  intro t ht
  simp only [Real.dist_eq, sub_zero, lt_min_iff] at ht
  rw [show correction 0 = 0 by simp [correction]]
  simp only [Real.dist_eq, sub_zero]
  have hb := correction_abs_bound ht.1.le
  have hh := (lt_div_iff₀ Real.pi_pos).mp ht.2
  nlinarith

theorem correction_continuous : correctionContinuous := by
  intro t ht
  by_cases hz : t = 0
  · subst t
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    refine ⟨ε / Real.pi, div_pos hε Real.pi_pos, ?_⟩
    intro x hx hd
    simp only [Real.dist_eq, sub_zero] at hd
    have hb := correction_bound hx.1 hx.2
    rw [show correction 0 = 0 by simp [correction]]
    simp only [Real.dist_eq, sub_zero]
    have hx' := (abs_lt.mp hd).2
    have := (lt_div_iff₀ Real.pi_pos).mp hx'
    nlinarith
  · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
    have hs := Real.sin_pos_of_pos_of_lt_pi (show 0 < t/2 by linarith)
      (show t/2 < Real.pi by linarith [ht.2, Real.pi_pos])
    exact (((continuousAt_const.div
      (Real.continuous_sin.continuousAt.comp (continuousAt_id.div_const 2)) hs.ne').sub
      (continuousAt_const.div continuousAt_id hz)) : ContinuousAt correction t).continuousWithinAt
/-- The real finite kernel agrees with the corrected sinc expression on the
positive half-period. No singular value is assigned to the finite kernel. -/
theorem kernel_sinc_decomposition (N : ℕ) {t : ℝ} (ht : 0 < t) (hp : t ≤ Real.pi) :
    (dirichletKernel N t).re =
      2 * (((N : ℝ)+1/2) * Real.sinc (((N : ℝ)+1/2)*t)) +
        correction t * Real.sin (((N : ℝ)+1/2)*t) := by
  have hν : 0 < (N : ℝ)+1/2 := by positivity
  have hs : Real.sin (t/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have he := congrArg Complex.re (dirichletKernel_sine_mul N t)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  rw [Real.sinc_of_ne_zero (mul_pos hν ht).ne']
  unfold correction
  apply (mul_left_cancel₀ hs)
  rw [he]
  field_simp
  ring

theorem correction_integral_bound {u v ν : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ Real.pi) :
    ∃ h : RealIntegrable (fun t => correction t * Real.sin (ν*t)) u v,
      |realIntegral _ h| ≤ Real.pi^3 := by
  have hc : ContinuousOn correction (Icc u v) := correction_continuous.mono
    (fun _ hx => ⟨hu.trans hx.1, hx.2.trans hv⟩)
  have hg : RealIntegrable (fun t => correction t * Real.sin (ν*t)) u v := continuous_integrable huv (hc.mul
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
  refine ⟨hg, ?_⟩
  obtain ⟨hn, hn₁, _⟩ := real_norm_estimate _ hg
  have hb : ∀ x ∈ Icc u v, ‖correction x * Real.sin (ν*x)‖ ≤ Real.pi^2 := by
    intro x hx
    rw [Real.norm_eq_abs, abs_mul]
    have hc := correction_bound (hu.trans hx.1) (hx.2.trans hv)
    have hs := Real.abs_sin_le_one (ν*x)
    calc
      _ ≤ |correction x| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ ≤ Real.pi * x := by simpa using hc
      _ ≤ Real.pi^2 := by nlinarith [hx.2.trans hv, Real.pi_pos]
  have he := realIntegral_le_mul_bound hn hb
  have hlen : v-u ≤ Real.pi := by linarith
  have hpow : (v-u) * Real.pi^2 ≤ Real.pi^3 := by
    nlinarith [mul_le_mul_of_nonneg_right hlen (sq_nonneg Real.pi)]
  change |realIntegral _ hg| ≤ _ at hn₁
  exact hn₁.trans (he.trans hpow)

theorem dirichlet_kernel_primitive_bound : kernelPrimitiveBound := by
  refine ⟨8 + Real.pi^3, by positivity, ?_⟩
  intro N u v hu huv hv
  let ν : ℝ := (N : ℝ)+1/2
  have hν : 0 < ν := by dsimp [ν]; positivity
  obtain ⟨hs, hsB⟩ := scaled_sinc_bound hν hu huv
  obtain ⟨he, heB⟩ := correction_integral_bound (ν := ν) hu huv hv
  obtain ⟨h2s, h2sE⟩ := real_mul_value hs 2
  obtain ⟨hf, hfE⟩ := real_add_value h2s he
  have hk : ComplexIntegrable (dirichletKernel N) u v :=
    complexIntegrable_of_continuousOn huv (dirichletKernel_continuous N).continuousOn
  refine ⟨hk, ?_⟩
  have hr : realIntegral (fun t => (dirichletKernel N t).re) hk.1 = realIntegral _ hf := by
    apply integral_congr hk.1 hf
    intro t ht
    exact kernel_sinc_decomposition N (by linarith [ht.1]) (ht.2.le.trans hv)
  have hb : |realIntegral (fun t => (dirichletKernel N t).re) hk.1| ≤ 8 + Real.pi^3 := by
    rw [hr, hfE, h2sE]
    calc
      _ ≤ |2 * realIntegral _ hs| + |realIntegral _ he| := abs_add_le _ _
      _ ≤ 8 + Real.pi^3 := by rw [abs_mul]; norm_num; linarith
  obtain ⟨hz, hzE⟩ := real_zero_value huv
  have him : (fun t => (dirichletKernel N t).im) = fun _ => 0 :=
    funext (dirichletKernel_real N)
  change ‖complexIntegral (dirichletKernel N) hk‖ ≤ _
  rw [integral_re_im hk hk.1 hz rfl him, hzE]
  simpa only [Complex.ofReal_zero, zero_mul, add_zero, Complex.norm_real,
    Real.norm_eq_abs] using hb

end SingleVariableAnalysis.Fourier
