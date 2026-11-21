import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.PeriodicWirtinger
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.IntervalL2Constants

noncomputable section
open MeasureTheory Set Complex AddCircle
open scoped Topology

namespace VariationalNotes.Classical.PeriodicWirtinger
open ExpandedFA.PartIV.IntervalL2

private lemma continuous_memLp_interval {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x (Ioc_subset_Icc_self hx)

/-- Period-two estimate, retaining the necessary equality information pointwise. -/
lemma period_two {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : f 1 = f (-1)) (hm : (∫ x in (-1 : ℝ)..1, f x) = 0) :
    Real.pi ^ 2 * (∫ x in (-1 : ℝ)..1, |f x| ^ 2) ≤
        (∫ x in (-1 : ℝ)..1, |deriv f x| ^ 2) ∧
    (Real.pi ^ 2 * (∫ x in (-1 : ℝ)..1, |f x| ^ 2) =
        (∫ x in (-1 : ℝ)..1, |deriv f x| ^ 2) →
      ∃ A B : ℝ, EqOn f (fun x => A * Real.cos (Real.pi * x) +
        B * Real.sin (Real.pi * x)) (Icc (-1) 1)) := by
  let F : ℝ → ℂ := fun x => (f x : ℂ)
  let G : ℝ → ℂ := fun x => ((deriv f x : ℝ) : ℂ)
  have hF : ContDiff ℝ 1 F := Complex.ofRealCLM.contDiff.comp hf
  have hG : Continuous G := Complex.continuous_ofReal.comp (hf.continuous_deriv (by norm_num))
  have hd : ∀ᵐ x ∂volume, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt F (G x) x := by
    exact Filter.Eventually.of_forall (fun x _ =>
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        ((hf.differentiable (by norm_num)) x).hasDerivAt)
  have hmF : (∫ x in (-1 : ℝ)..1, F x) = 0 := by
    change (∫ x in (-1 : ℝ)..1, Complex.ofRealCLM (f x)) = 0
    rw [Complex.ofRealCLM.intervalIntegral_comp_comm
      (hf.continuous.intervalIntegrable _ _), hm, map_zero]
  have hh := period_two_ac_spectral_gap hF.contDiffOn.absolutelyContinuousOnInterval
    (continuous_memLp_interval hF.continuous) (continuous_memLp_interval hG) hd
    (by simp [F, hp]) hmF
  have hnormF (x : ℝ) : ‖F x‖ = |f x| := by simp [F]
  have hnormG (x : ℝ) : ‖G x‖ = |deriv f x| := by simp [G]
  simp only [hnormF, hnormG] at hh
  refine ⟨hh.1, ?_⟩
  intro he
  have hcoeff := hh.2.mp he
  have ha := two_mode_representation (continuous_memLp_interval hF.continuous) hcoeff
  let p := fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) F 1
  let q := fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) F (-1)
  let E : ℝ → ℂ := fun x => p * fourier 1 (x : AddCircle (2 : ℝ)) +
    q * fourier (-1) (x : AddCircle (2 : ℝ))
  have hE : Continuous E :=
    (continuous_const.mul ((fourier 1).continuous.comp (AddCircle.continuous_mk' _))).add
      (continuous_const.mul ((fourier (-1)).continuous.comp (AddCircle.continuous_mk' _)))
  have hae : F =ᵐ[volume.restrict (Icc (-1 : ℝ) 1)] E := by
    rwa [restrict_Ioc_eq_restrict_Icc] at ha
  have hpoint := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (-1 : ℝ) ≠ 1)
    hae hF.continuous.continuousOn hE.continuousOn
  refine ⟨(p + q).re, ((p - q) * I).re, ?_⟩
  intro x hx
  have hz := hpoint hx
  change (f x : ℂ) = p * fourier 1 (x : AddCircle (2 : ℝ)) +
    q * fourier (-1) (x : AddCircle (2 : ℝ)) at hz
  rw [fourier_one_trig, fourier_neg_one_trig] at hz
  have halg : p * ((Real.cos (Real.pi * x) : ℂ) + (Real.sin (Real.pi * x) : ℂ) * I) +
      q * ((Real.cos (Real.pi * x) : ℂ) - (Real.sin (Real.pi * x) : ℂ) * I) =
      (p + q) * (Real.cos (Real.pi * x) : ℂ) +
      ((p - q) * I) * (Real.sin (Real.pi * x) : ℂ) := by ring
  rw [halg] at hz
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re, Complex.sub_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, zero_add, sub_self,
    zero_sub] using congrArg Complex.re hz

/-- The first harmonic has the asserted energy for any positive period. -/
lemma harmonic_energy (T A B : ℝ) (hT : 0 < T) :
    let H := fun t : ℝ => A * Real.cos (2 * Real.pi * t / T) +
      B * Real.sin (2 * Real.pi * t / T)
    (∫ t in (0 : ℝ)..T, |H t| ^ 2) =
      (T / (2 * Real.pi)) ^ 2 * (∫ t in (0 : ℝ)..T, |deriv H t| ^ 2) := by
  let w := 2 * Real.pi / T
  let H := fun t : ℝ => A * Real.cos (w * t) + B * Real.sin (w * t)
  let D := fun t : ℝ => -A * w * Real.sin (w * t) + B * w * Real.cos (w * t)
  have hH (t : ℝ) : HasDerivAt H (D t) t := by
    apply HasDerivAt.congr_deriv ((((Real.hasDerivAt_cos (w * t)).comp t
      ((hasDerivAt_id t).const_mul w)).const_mul A).add
      (((Real.hasDerivAt_sin (w * t)).comp t
      ((hasDerivAt_id t).const_mul w)).const_mul B))
    dsimp [D]
    ring
  have hD (t : ℝ) : HasDerivAt D (-w ^ 2 * H t) t := by
    apply HasDerivAt.congr_deriv ((((Real.hasDerivAt_sin (w * t)).comp t
      ((hasDerivAt_id t).const_mul w)).const_mul (-A * w)).add
      (((Real.hasDerivAt_cos (w * t)).comp t
      ((hasDerivAt_id t).const_mul w)).const_mul (B * w)))
    dsimp [H]
    ring
  have hcH : Continuous H := by fun_prop
  have hcD : Continuous D := by fun_prop
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hH x) (fun x _ => hD x)
    (hcD.intervalIntegrable 0 T)
    ((continuous_const.mul hcH).intervalIntegrable 0 T)
  have hwT : w * T = 2 * Real.pi := by dsimp [w]; field_simp
  have heH : H T = H 0 := by simp [H, hwT, Real.cos_two_pi, Real.sin_two_pi]
  have heD : D T = D 0 := by simp [D, hwT, Real.cos_two_pi, Real.sin_two_pi]
  rw [heH, heD, sub_self] at hi
  have he : (∫ t in (0 : ℝ)..T, D t ^ 2) =
      w ^ 2 * (∫ t in (0 : ℝ)..T, H t ^ 2) := by
    calc
      _ = -(∫ t in (0 : ℝ)..T, H t * (-w ^ 2 * H t)) := by
        have hh := hi
        simp only [← pow_two, zero_sub] at hh
        linarith
      _ = w ^ 2 * (∫ t in (0 : ℝ)..T, H t ^ 2) := by
        simp_rw [show ∀ t, H t * (-w ^ 2 * H t) = -w ^ 2 * H t ^ 2 by intro t; ring]
        rw [intervalIntegral.integral_const_mul]
        ring
  have hh : (fun t => A * Real.cos (2 * Real.pi * t / T) +
      B * Real.sin (2 * Real.pi * t / T)) = H := by
    funext t
    dsimp [H, w]
    congr 2 <;> ring
  dsimp only
  rw [hh]
  simp_rw [sq_abs, (hH _).deriv]
  rw [he]
  have hw : (T / (2 * Real.pi)) ^ 2 * w ^ 2 = 1 := by
    dsimp [w]
    field_simp
  rw [← mul_assoc, hw, one_mul]
  exact congrArg (fun K : ℝ → ℝ => ∫ t in (0 : ℝ)..T, K t ^ 2) hh

private lemma harmonic_periodic (T A B : ℝ) (hT : T ≠ 0) :
    Function.Periodic (fun t => A * Real.cos (2 * Real.pi * t / T) +
      B * Real.sin (2 * Real.pi * t / T)) T := by
  intro t
  have he : 2 * Real.pi * (t + T) / T = 2 * Real.pi * t / T + 2 * Real.pi := by
    field_simp
  simp only [he, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The general period is obtained by an affine change of variable from [-1,1]. -/
theorem periodic_wirtinger : Specs.VariationalNotes.Classical.PeriodicWirtinger.Statement := by
  intro T hT f ⟨hf, hp, hm⟩
  let c := T / 2
  have hc : 0 < c := by dsimp [c]; positivity
  let F : ℝ → ℝ := fun x => f (c * x + c)
  have hF : ContDiff ℝ 1 F := hf.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  have hd (x : ℝ) : deriv F x = c * deriv f (c * x + c) := by
    have h := ((hf.differentiable (by norm_num)) (c * x + c)).hasDerivAt.comp x
      (((hasDerivAt_id x).const_mul c).add_const c)
    simpa [F, mul_comm, Function.comp_def] using h.deriv
  have hchange (g : ℝ → ℝ) :
      (∫ x in (-1 : ℝ)..1, g (c * x + c)) =
        c⁻¹ * (∫ t in (0 : ℝ)..T, g t) := by
    have he := intervalIntegral.integral_comp_mul_add (a := (-1 : ℝ)) (b := 1) g hc.ne' c
    simpa [c, smul_eq_mul] using he
  have hmean : (∫ x in (-1 : ℝ)..1, F x) = 0 := by
    rw [show F = (fun x => f (c * x + c)) from rfl, hchange, hm, mul_zero]
  have hend : F 1 = F (-1) := by
    simpa [F, c] using hp.eq
  have henergyF : (∫ x in (-1 : ℝ)..1, |F x| ^ 2) =
      c⁻¹ * (∫ t in (0 : ℝ)..T, |f t| ^ 2) := hchange (fun t => |f t| ^ 2)
  have henergyD : (∫ x in (-1 : ℝ)..1, |deriv F x| ^ 2) =
      c * (∫ t in (0 : ℝ)..T, |deriv f t| ^ 2) := by
    simp_rw [hd, abs_mul, mul_pow, sq_abs]
    rw [intervalIntegral.integral_const_mul, hchange (fun t => deriv f t ^ 2), ← mul_assoc]
    congr 1
    field_simp [hc.ne']
  obtain ⟨hineq, heq⟩ := period_two hF hend hmean
  rw [henergyF, henergyD] at hineq heq
  let X := ∫ t in (0 : ℝ)..T, |f t| ^ 2
  let Y := ∫ t in (0 : ℝ)..T, |deriv f t| ^ 2
  have hineq' : Real.pi ^ 2 * (c⁻¹ * X) ≤ c * Y := hineq
  have hbound : X ≤ (T / (2 * Real.pi)) ^ 2 * Y := by
    apply (mul_le_mul_iff_right₀ (show 0 < Real.pi ^ 2 / c by positivity)).mp
    convert hineq' using 1 <;> dsimp [c] <;> field_simp
  refine ⟨hbound, ?_⟩
  constructor
  · intro he
    have he' : Real.pi ^ 2 * (c⁻¹ * X) = c * Y := by
      change X = (T / (2 * Real.pi)) ^ 2 * Y at he
      rw [he]
      dsimp [c]
      field_simp
    obtain ⟨A, B, hab⟩ := heq he'
    refine ⟨-A, -B, ?_⟩
    have hlocal : EqOn f (fun t => -A * Real.cos (2 * Real.pi * t / T) +
        -B * Real.sin (2 * Real.pi * t / T)) (Icc 0 T) := by
      intro t ht
      let x := 2 * t / T - 1
      have hx : x ∈ Icc (-1 : ℝ) 1 := by
        dsimp [x]
        constructor
        · have := div_nonneg (by linarith [ht.1] : 0 ≤ 2 * t) hT.le
          linarith
        · have : 2 * t / T ≤ 2 := (div_le_iff₀ hT).mpr (by linarith [ht.2])
          linarith
      have harg : c * x + c = t := by dsimp [c, x]; field_simp; ring
      have hphase : Real.pi * x = 2 * Real.pi * t / T - Real.pi := by
        dsimp [x]; ring
      have hh := hab hx
      change f (c * x + c) = A * Real.cos (Real.pi * x) + B * Real.sin (Real.pi * x) at hh
      rw [harg, hphase, Real.cos_sub, Real.sin_sub] at hh
      simpa only [Real.cos_pi, Real.sin_pi, mul_neg_one, mul_zero,
        add_zero, sub_zero, neg_mul, mul_neg, mul_one] using hh
    have hper := hp.sub (harmonic_periodic T (-A) (-B) hT.ne')
    intro t
    obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ hT t
    have hz : f y - (-A * Real.cos (2 * Real.pi * y / T) +
        -B * Real.sin (2 * Real.pi * y / T)) = 0 := sub_eq_zero.mpr (hlocal ⟨hy.1, hy.2.le⟩)
    exact sub_eq_zero.mp (hty.trans hz)
  · rintro ⟨A, B, hab⟩
    have hfun : f = (fun t => A * Real.cos (2 * Real.pi * t / T) +
        B * Real.sin (2 * Real.pi * t / T)) := funext hab
    rw [hfun]
    exact harmonic_energy T A B hT

end VariationalNotes.Classical.PeriodicWirtinger
