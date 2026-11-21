import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.IsoperimetricInequality
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.GreenAreaBridge
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.PeriodicWirtinger
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology

namespace VariationalNotes.Classical.IsoperimetricInequality
open Specs.VariationalNotes.Classical.GreenAreaBridge
open Specs.VariationalNotes.Classical.IsoperimetricInequality
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.SmoothJordan

/-- A continuous prescribed one-sided velocity gives exactly C¹ regularity
on a nondegenerate closed interval. -/
lemma contDiffOn_of_velocity {a b : ℝ} {f v : ℝ → ℂ} (hab : a < b)
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt f (v t) (Icc a b) t) :
    ContDiffOn ℝ 1 f (Icc a b) := by
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mpr
  refine ⟨fun t ht => (hd t ht).differentiableWithinAt, ?_⟩
  apply hv.congr
  intro t ht
  exact (hd t ht).derivWithin (uniqueDiffOn_Icc hab t ht)

lemma memLp_of_continuousOn_interval {a b : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc a b)) : MemLp f 2 (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply MemLp.of_bound (hf.mono Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc) C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x (Ioc_subset_Icc_self hx)

/-- The complex version on a closed interval uses only one-sided C¹ data.
The Fourier theorem's probability/interval normalization is already included
in its interval spectral-gap statement. -/
lemma closed_interval_wirtinger {T : ℝ} {f v : ℝ → ℂ} (hT : 0 < T)
    (hC : C1Curve f v T) (hp : f 0 = f T)
    (hm : (∫ t in (0 : ℝ)..T, f t) = 0) :
    (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) ≤
      (T / (2 * Real.pi)) ^ 2 * (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) := by
  let c := T / 2
  have hc : 0 < c := by dsimp [c]; positivity
  let F : ℝ → ℂ := fun x => f (c * x + c)
  let V : ℝ → ℂ := fun x => c • v (c * x + c)
  have hmap : MapsTo (fun x : ℝ => c * x + c) (Icc (-1) 1) (Icc 0 T) := by
    intro x hx
    dsimp [c]
    constructor <;> nlinarith [hx.1, hx.2]
  have hF : ContinuousOn F (Icc (-1) 1) :=
    hC.1.comp (by fun_prop) hmap
  have hV : ContinuousOn V (Icc (-1) 1) :=
    (hC.2.1.comp (by fun_prop) hmap).const_smul c
  have hd : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt F (V x) (Icc (-1) 1) x := by
    intro x hx
    simpa [F, V, Function.comp_def] using (hC.2.2 _ (hmap hx)).scomp x
      ((((hasDerivAt_id x).const_mul c).add_const c).hasDerivWithinAt) hmap
  have hAC : AbsolutelyContinuousOnInterval F (-1) 1 := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact contDiffOn_of_velocity (by norm_num) hV hd
  have hdae : ∀ᵐ x ∂volume, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt F (V x) x := by
    filter_upwards [volume.ae_ne (-1 : ℝ), volume.ae_ne (1 : ℝ)] with x hx₀ hx₁ hx
    exact (hd x hx).hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne hx.1 hx₀.symm)
      (lt_of_le_of_ne hx.2 hx₁))
  have hchange (g : ℝ → ℂ) :
      (∫ x in (-1 : ℝ)..1, g (c * x + c)) = c⁻¹ • (∫ t in (0 : ℝ)..T, g t) := by
    simpa [c] using intervalIntegral.integral_comp_mul_add
      (a := (-1 : ℝ)) (b := 1) g hc.ne' c
  have hchangeR (g : ℝ → ℝ) :
      (∫ x in (-1 : ℝ)..1, g (c * x + c)) = c⁻¹ * (∫ t in (0 : ℝ)..T, g t) := by
    simpa [c, smul_eq_mul] using intervalIntegral.integral_comp_mul_add
      (a := (-1 : ℝ)) (b := 1) g hc.ne' c
  have hmean : (∫ x in (-1 : ℝ)..1, F x) = 0 := by
    rw [show F = (fun x => f (c * x + c)) from rfl, hchange, hm, smul_zero]
  have hend : F 1 = F (-1) := by simpa [F, c] using hp.symm
  have hs := (ExpandedFA.PartIV.IntervalL2.period_two_ac_spectral_gap hAC
    (memLp_of_continuousOn_interval hF) (memLp_of_continuousOn_interval hV)
    hdae hend hmean).1
  have hEF : (∫ x in (-1 : ℝ)..1, ‖F x‖ ^ 2) =
      c⁻¹ * (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) := hchangeR (fun t => ‖f t‖ ^ 2)
  have hEV : (∫ x in (-1 : ℝ)..1, ‖V x‖ ^ 2) =
      c * (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) := by
    simp_rw [V, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [intervalIntegral.integral_const_mul, hchangeR (fun t => ‖v t‖ ^ 2), ← mul_assoc]
    congr 1
    field_simp [hc.ne']
  rw [hEF, hEV] at hs
  apply (mul_le_mul_iff_right₀ (show 0 < Real.pi ^ 2 / c by positivity)).mp
  convert hs using 1 <;> dsimp [c] <;> field_simp

/-- The squared defect from the equality ODE. -/
lemma defect_integral {T k : ℝ} {f v : ℝ → ℂ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T)) :
    (∫ t in (0 : ℝ)..T, ‖J0 (f t) - k • v t‖ ^ 2) =
      (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) -
      2 * k * (∫ t in (0 : ℝ)..T, boundaryIntegrand f v t) +
      k ^ 2 * (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) := by
  have hJ : Continuous (J0 : ℂ → ℂ) := by unfold J0; fun_prop
  have hiF : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 T :=
    (hf.norm.pow 2).intervalIntegrable_of_Icc hT
  have hiV : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 T :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hT
  have hiB : IntervalIntegrable (boundaryIntegrand f v) volume 0 T :=
    ((hJ.comp_continuousOn hf).inner hv).intervalIntegrable_of_Icc hT
  have hid (t : ℝ) : ‖J0 (f t) - k • v t‖ ^ 2 =
      ‖f t‖ ^ 2 - 2 * k * boundaryIntegrand f v t + k ^ 2 * ‖v t‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul]
    simp only [J0, norm_mul, Complex.norm_I, one_mul, Real.norm_eq_abs, mul_pow, sq_abs,
      boundaryIntegrand]
    ring
  simp_rw [hid]
  rw [intervalIntegral.integral_add (hiF.sub (hiB.const_mul _)) (hiV.const_mul _),
    intervalIntegral.integral_sub hiF (hiB.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The integral mean can be subtracted without any global extension. -/
lemma centered_curve {T : ℝ} {γ v : ℝ → ℂ} (hT : 0 < T)
    (hC : C1Curve γ v T) (hp : γ 0 = γ T) :
    let m := T⁻¹ • (∫ t in (0 : ℝ)..T, γ t)
    C1Curve (fun t => γ t - m) v T ∧
    (γ 0 - m = γ T - m) ∧
    (∫ t in (0 : ℝ)..T, γ t - m) = 0 := by
  dsimp only
  refine ⟨⟨hC.1.sub continuousOn_const, hC.2.1, fun t ht => (hC.2.2 t ht).sub_const _⟩,
    congrArg (fun z : ℂ => z - T⁻¹ • (∫ t in (0 : ℝ)..T, γ t)) hp, ?_⟩
  rw [intervalIntegral.integral_sub (hC.1.intervalIntegrable_of_Icc hT.le)
    (intervalIntegrable_const), intervalIntegral.integral_const]
  simp [hT.ne']

/-- The sharp planar estimate for a closed C¹ unit-speed traversal.
Completing a square retains the pointwise equality ODE. -/
lemma unit_speed_area_bound_and_defect {T A : ℝ} {γ v : ℝ → ℂ} (hT : 0 < T)
    (hC : C1Curve γ v T) (hp : γ 0 = γ T)
    (hunit : ∀ t ∈ Icc 0 T, ‖v t‖ = 1)
    (hA : A = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t) :
    4 * Real.pi * A ≤ T ^ 2 ∧
      (4 * Real.pi * A = T ^ 2 → ∀ t ∈ Icc 0 T,
        J0 (γ t - T⁻¹ • (∫ s in (0 : ℝ)..T, γ s)) =
          (T / (2 * Real.pi)) • v t) := by
  let m := T⁻¹ • (∫ t in (0 : ℝ)..T, γ t)
  let f : ℝ → ℂ := fun t => γ t - m
  obtain ⟨hCf, hpf, hmf⟩ := centered_curve hT hC hp
  change C1Curve f v T at hCf
  change f 0 = f T at hpf
  change (∫ t in (0 : ℝ)..T, f t) = 0 at hmf
  have hW := closed_interval_wirtinger hT hCf hpf hmf
  have htrans := GreenAreaBridge.translation_invariance T γ v hT.le hC hp m
  have hY : (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) = T := by
    calc
      _ = ∫ _t in (0 : ℝ)..T, (1 : ℝ) := intervalIntegral.integral_congr
        (fun t ht => by rw [hunit t (by simpa [uIcc_of_le hT.le] using ht)]; norm_num)
      _ = T := by simp
  have hB : (∫ t in (0 : ℝ)..T, boundaryIntegrand f v t) = 2 * A := by
    change (∫ t in (0 : ℝ)..T, boundaryIntegrand (fun t => γ t - m) v t) = _
    rw [htrans]
    linarith [hA]
  have hD := defect_integral (k := T / (2 * Real.pi)) hT.le hCf.1 hCf.2.1
  have hpos : 0 ≤ ∫ t in (0 : ℝ)..T,
      ‖J0 (f t) - (T / (2 * Real.pi)) • v t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT.le (fun _ _ => sq_nonneg _)
  rw [hY, hB] at hD
  rw [hY] at hW
  have hk : 0 < T / (2 * Real.pi) := by positivity
  have hlin : 4 * (T / (2 * Real.pi)) * A ≤ 2 * (T / (2 * Real.pi)) ^ 2 * T := by
    linarith only [hD, hpos, hW]
  have he : 2 * (T / (2 * Real.pi)) * Real.pi = T := by field_simp
  have hh := (mul_le_mul_iff_right₀ hk).mp (show
      (T / (2 * Real.pi)) * (4 * A) ≤
        (T / (2 * Real.pi)) * (2 * (T / (2 * Real.pi)) * T) by nlinarith only [hlin])
  refine ⟨?_, ?_⟩
  · calc
      4 * Real.pi * A = (4 * A) * Real.pi := by ring
      _ ≤ (2 * (T / (2 * Real.pi)) * T) * Real.pi :=
        mul_le_mul_of_nonneg_right hh Real.pi_pos.le
      _ = T ^ 2 := by field_simp
  · intro heq
    have hAval : A = T ^ 2 / (4 * Real.pi) := by
      apply (eq_div_iff (by positivity : (4 * Real.pi : ℝ) ≠ 0)).mpr
      nlinarith only [heq]
    have hbalance : 4 * (T / (2 * Real.pi)) * A =
        2 * (T / (2 * Real.pi)) ^ 2 * T := by
      rw [hAval]
      field_simp
    have hzero : (∫ t in (0 : ℝ)..T,
        ‖J0 (f t) - (T / (2 * Real.pi)) • v t‖ ^ 2) = 0 := by
      linarith only [hD, hpos, hW, hbalance]
    have hJ : Continuous (J0 : ℂ → ℂ) := by unfold J0; fun_prop
    have hcont : ContinuousOn (fun t => ‖J0 (f t) - (T / (2 * Real.pi)) • v t‖ ^ 2)
        (Icc 0 T) :=
      ((hJ.comp_continuousOn hCf.1).sub (hCf.2.1.const_smul (T / (2 * Real.pi)))).norm.pow 2
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
      (μ := volume) (f := fun t => ‖J0 (f t) - (T / (2 * Real.pi)) • v t‖ ^ 2) hT.le
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (hcont.intervalIntegrable_of_Icc hT.le)).mp hzero
    rw [restrict_Ioc_eq_restrict_Icc] at hae
    have hpoint := Measure.eqOn_Icc_of_ae_eq volume hT.ne hae hcont continuousOn_const
    intro t ht
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hsq := hpoint ht
    simpa only [Pi.zero_apply, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)] using hsq

lemma unit_speed_area_bound {T A : ℝ} {γ v : ℝ → ℂ} (hT : 0 < T)
    (hC : C1Curve γ v T) (hp : γ 0 = γ T)
    (hunit : ∀ t ∈ Icc 0 T, ‖v t‖ = 1)
    (hA : A = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t) :
    4 * Real.pi * A ≤ T ^ 2 :=
  (unit_speed_area_bound_and_defect hT hC hp hunit hA).1

/-- Solve the constant angular-velocity equation with an integrating
factor, using derivatives only within the closed parameter interval. -/
lemma rotation_solution {T ω : ℝ} {f : ℝ → ℂ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f
      (((ω : ℂ) * Complex.I) * f t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, f t = Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * f 0 := by
  let E : ℝ → ℂ := fun t => Complex.exp (-((ω : ℂ) * Complex.I) * (t : ℂ))
  have hdE (t : ℝ) : HasDerivAt E
      (E t * (-((ω : ℂ) * Complex.I))) t := by
    simpa [E] using ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_id t)).const_mul (-((ω : ℂ) * Complex.I))).cexp
  have hzero : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => f t * E t) 0 (Icc 0 T) t := by
    intro t ht
    convert (hd t ht).mul (hdE t).hasDerivWithinAt using 1; ring
  intro t ht
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hzero
    (C := 0) (fun _ _ => by simp) (convex_Icc 0 T) (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht
  have he : f t * E t = f 0 := by
    have hh : f t * E t = f 0 * E 0 := by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
    simpa [E] using hh
  have hinv : E t * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) = 1 := by
    dsimp only [E]
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring
  calc
    f t = (f t * E t) * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) := by rw [mul_assoc, hinv, mul_one]
    _ = _ := by rw [he, mul_comm]

/-- A full positive turn of a nonzero rotating vector traces exactly a
circle, including every point of that circle. -/
lemma rotation_image {T : ℝ} (hT : 0 < T) (a m : ℂ) :
    (fun t : ℝ => m + Complex.exp ((((2 * Real.pi / T) * t : ℝ) : ℂ) * Complex.I) * a) '' Icc 0 T =
      Metric.sphere m ‖a‖ := by
  let F : ℝ → ℂ := fun t => m + Complex.exp ((((2 * Real.pi / T) * t : ℝ) : ℂ) * Complex.I) * a
  have hp : Function.Periodic F T := by
    intro t
    have harg : ((((2 * Real.pi / T) * (t + T) : ℝ) : ℂ) * Complex.I) =
        ((((2 * Real.pi / T) * t : ℝ) : ℂ) * Complex.I) + 2 * Real.pi * Complex.I := by
      have hreal : (2 * Real.pi / T) * (t + T) = (2 * Real.pi / T) * t + 2 * Real.pi := by
        field_simp
      rw [hreal, Complex.ofReal_add, add_mul]
      push_cast
      rfl
    dsimp [F]
    rw [harg, Complex.exp_add]
    simp
  change F '' Icc 0 T = _
  rw [show Icc 0 T = Icc 0 (0 + T) by simp, hp.image_Icc hT]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [Metric.mem_sphere, dist_eq_norm]
    change ‖(m + Complex.exp (↑(2 * Real.pi / T * t) * Complex.I) * a) - m‖ = ‖a‖
    rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  · intro hz
    have hz' : ‖z - m‖ = ‖a‖ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    by_cases ha : a = 0
    · have hzm : z = m := by simpa [ha, sub_eq_zero] using hz'
      refine ⟨0, ?_⟩
      simp [F, ha, hzm]
    · have hnorm : ‖(z - m) / a‖ = 1 := by rw [norm_div, hz', div_self (norm_ne_zero_iff.mpr ha)]
      obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff _).mp hnorm
      refine ⟨θ * T / (2 * Real.pi), ?_⟩
      have hcancel : (2 * Real.pi / T) * (θ * T / (2 * Real.pi)) = θ := by field_simp
      dsimp [F]
      rw [hcancel, hθ, div_mul_cancel₀ _ ha]
      ring

/-- Equality in the analytic estimate identifies the full geometric
image, with strictly positive radius. -/
lemma equality_implies_circle {c : Specs.D13Unified.Ch21.Collar.Circle → ℂ} {T A : ℝ} {γ v : ℝ → ℂ}
    (hparam : ArcLengthParametrization c T γ v)
    (hA : A = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t)
    (heq : 4 * Real.pi * A = T ^ 2) : IsCircle c := by
  obtain ⟨hT, hlen, hC, hp, hvp, hinj, htrace, hunit⟩ := hparam
  let m := T⁻¹ • (∫ t in (0 : ℝ)..T, γ t)
  let f : ℝ → ℂ := fun t => γ t - m
  let k := T / (2 * Real.pi)
  have hk : 0 < k := by dsimp [k]; positivity
  have hdef := (unit_speed_area_bound_and_defect hT hC hp hunit hA).2 heq
  change ∀ t ∈ Icc 0 T, J0 (f t) = k • v t at hdef
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hnorm : ‖f 0‖ = k := by
    have hh := congrArg norm (hdef 0 h0)
    simpa only [J0, norm_mul, Complex.norm_I, one_mul, norm_smul,
      Real.norm_eq_abs, abs_of_pos hk, hunit 0 h0, mul_one] using hh
  have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f
      ((((2 * Real.pi / T : ℝ) : ℂ) * Complex.I) * f t) (Icc 0 T) t := by
    intro t ht
    have hv : v t = k⁻¹ • J0 (f t) := by
      rw [hdef t ht, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
    have hkω : k⁻¹ = 2 * Real.pi / T := by dsimp [k]; field_simp
    have hval : v t = (((2 * Real.pi / T : ℝ) : ℂ) * Complex.I) * f t := by
      rw [hv, hkω]
      change ((2 * Real.pi / T : ℝ) : ℂ) * (Complex.I * f t) = _
      ring
    rw [← hval]
    exact (hC.2.2 t ht).sub_const m
  have hsol := rotation_solution hT.le hd
  have himage : γ '' Icc 0 T =
      (fun t : ℝ => m + Complex.exp ((((2 * Real.pi / T) * t : ℝ) : ℂ) * Complex.I) * f 0) '' Icc 0 T := by
    apply image_congr
    intro t ht
    have hh := hsol t ht
    change γ t - m = _ at hh
    exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)
  refine ⟨m, ‖f 0‖, hnorm ▸ hk, ?_⟩
  rw [← htrace, himage, rotation_image hT]

lemma complex_real_inner (z w : ℂ) :
    inner ℝ z w = z.re * w.re + z.im * w.im := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The tangent and quarter-turned tangent are an orthogonal coordinate
frame; the formula does not divide by the norm. -/
lemma quarter_turn_decomposition (z w : ℂ) :
    ‖z‖ ^ 2 • w = (inner ℝ z w) • z + (inner ℝ (J0 z) w) • J0 z := by
  apply Complex.ext <;>
    simp [Complex.sq_norm, Complex.normSq_apply, J0,
      Complex.mul_re, Complex.mul_im] <;> ring

lemma quarter_turn_inner_sq (z w : ℂ) :
    (inner ℝ z w) ^ 2 + (inner ℝ (J0 z) w) ^ 2 = ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
  simp [Complex.sq_norm, Complex.normSq_apply, J0,
    Complex.mul_re, Complex.mul_im]
  ring

/-- A positive-area unit-speed traversal lying on a circle travels in
the positive tangent direction everywhere. -/
lemma circle_positive_tangent {T A r : ℝ} {γ v : ℝ → ℂ} {z : ℂ}
    (hT : 0 < T) (hApos : 0 < A) (hr : 0 < r)
    (hC : C1Curve γ v T) (hp : γ 0 = γ T)
    (hunit : ∀ t ∈ Icc 0 T, ‖v t‖ = 1)
    (hnorm : ∀ t ∈ Icc 0 T, ‖γ t - z‖ = r)
    (hA : A = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t) :
    ∀ t ∈ Icc 0 T, inner ℝ (J0 (γ t - z)) (v t) = r := by
  let f : ℝ → ℂ := fun t => γ t - z
  let b : ℝ → ℝ := fun t => inner ℝ (J0 (f t)) (v t)
  have horth : ∀ t ∈ Icc 0 T, inner ℝ (f t) (v t) = 0 := by
    intro t ht
    have hd := ((hC.2.2 t ht).sub_const z).norm_sq
    have hconst : HasDerivWithinAt (fun t => ‖γ t - z‖ ^ 2) 0 (Icc 0 T) t := by
      apply (hasDerivWithinAt_const t (Icc 0 T) (r ^ 2)).congr_of_mem _ ht
      intro s hs
      rw [hnorm s hs]
    have heq := (hd.derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
      (hconst.derivWithin (uniqueDiffOn_Icc hT t ht))
    change 2 * inner ℝ (f t) (v t) = 0 at heq
    linarith only [heq]
  have hsq : EqOn (b ^ 2) ((fun _ => r) ^ 2) (Icc 0 T) := by
    intro t ht
    have hh := quarter_turn_inner_sq (f t) (v t)
    rw [horth t ht, show ‖f t‖ = r from hnorm t ht, hunit t ht] at hh
    simpa [b] using hh
  have hJ : Continuous (J0 : ℂ → ℂ) := by unfold J0; fun_prop
  have hb : ContinuousOn b (Icc 0 T) :=
    (hJ.comp_continuousOn (hC.1.sub continuousOn_const)).inner hC.2.1
  have hchoices := isPreconnected_Icc.eq_or_eq_neg_of_sq_eq hb
    (continuousOn_const (c := r)) hsq (fun _ => hr.ne')
  rcases hchoices with hpos | hneg
  · exact hpos
  · have hint : (∫ t in (0 : ℝ)..T, boundaryIntegrand (fun t => γ t - z) v t) = -r * T := by
      calc
        _ = ∫ _t in (0 : ℝ)..T, -r := intervalIntegral.integral_congr
          (fun t ht => hneg (by simpa [uIcc_of_le hT.le] using ht))
        _ = -r * T := by simp; ring
    rw [GreenAreaBridge.translation_invariance T γ v hT.le hC hp z] at hint
    have hnegA : A = -(r * T) / 2 := by linarith only [hA, hint]
    have hproduct : 0 < r * T := mul_pos hr hT
    exfalso
    linarith only [hApos, hnegA, hproduct]

/-- A circle traversal has constant angular speed equal to reciprocal radius. -/
lemma circle_velocity {T A r : ℝ} {γ v : ℝ → ℂ} {z : ℂ}
    (hT : 0 < T) (hApos : 0 < A) (hr : 0 < r)
    (hC : C1Curve γ v T) (hp : γ 0 = γ T)
    (hunit : ∀ t ∈ Icc 0 T, ‖v t‖ = 1)
    (hnorm : ∀ t ∈ Icc 0 T, ‖γ t - z‖ = r)
    (hA : A = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t) :
    ∀ t ∈ Icc 0 T, v t = r⁻¹ • J0 (γ t - z) := by
  have hb := circle_positive_tangent hT hApos hr hC hp hunit hnorm hA
  intro t ht
  have horth : inner ℝ (γ t - z) (v t) = 0 := by
    have hh := quarter_turn_inner_sq (γ t - z) (v t)
    rw [hb t ht, hnorm t ht, hunit t ht] at hh
    nlinarith only [hh, sq_nonneg (inner ℝ (γ t - z) (v t))]
  have hh := quarter_turn_decomposition (γ t - z) (v t)
  rw [hnorm t ht, horth, zero_smul, zero_add, hb t ht] at hh
  have hs := congrArg (fun w : ℂ => (r ^ 2)⁻¹ • w) hh
  simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), one_smul] at hs
  have hcancel : (r ^ 2)⁻¹ * r = r⁻¹ := by field_simp
  simpa only [hcancel] using hs

/-- A single positive unit-speed traversal of a circle makes exactly
one full turn. This step is what allows arbitrary original embeddings. -/
lemma circle_implies_equality {c : Specs.D13Unified.Ch21.Collar.Circle → ℂ}
    {T A : ℝ} {γ v : ℝ → ℂ}
    (hparam : ArcLengthParametrization c T γ v) (hApos : 0 < A)
    (hA : A = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t)
    (hcircle : IsCircle c) : 4 * Real.pi * A = T ^ 2 := by
  obtain ⟨hT, hlen, hC, hp, hvp, hinj, htrace, hunit⟩ := hparam
  obtain ⟨z, r, hr, hcircle⟩ := hcircle
  have hnorm : ∀ t ∈ Icc 0 T, ‖γ t - z‖ = r := by
    intro t ht
    have hh : γ t ∈ Metric.sphere z r := hcircle ▸ (htrace ▸ mem_image_of_mem γ ht)
    simpa only [Metric.mem_sphere, dist_eq_norm] using hh
  have hvel := circle_velocity hT hApos hr hC hp hunit hnorm hA
  let f : ℝ → ℂ := fun t => γ t - z
  have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f
      ((((r⁻¹ : ℝ) : ℂ) * Complex.I) * f t) (Icc 0 T) t := by
    intro t ht
    have hv : v t = (((r⁻¹ : ℝ) : ℂ) * Complex.I) * f t := by
      rw [hvel t ht]
      change ((r⁻¹ : ℝ) : ℂ) * (Complex.I * f t) = _
      ring
    rw [← hv]
    exact (hC.2.2 t ht).sub_const z
  have hsol := rotation_solution hT.le hd
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hTf : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hf0 : f 0 ≠ 0 := norm_ne_zero_iff.mp (by simpa only [f, hnorm 0 h0] using hr.ne')
  have hexp : Complex.exp (((r⁻¹ * T : ℝ) : ℂ) * Complex.I) = 1 := by
    apply mul_right_cancel₀ hf0
    rw [one_mul, ← hsol T hTf]
    exact congrArg (fun w : ℂ => w - z) hp.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hphase : r⁻¹ * T = (n : ℝ) * (2 * Real.pi) := by
    have hh := congrArg Complex.im hn
    simpa using hh
  have hnpos : 0 < (n : ℝ) := by
    apply (mul_pos_iff_of_pos_right Real.two_pi_pos).mp
    rw [← hphase]
    exact mul_pos (inv_pos.mpr hr) hT
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by
    have hnInt : (0 : ℤ) < n := by exact_mod_cast hnpos
    exact_mod_cast (Int.add_one_le_iff.mpr hnInt : (0 : ℤ) + 1 ≤ n)
  let p := 2 * Real.pi * r
  have hpPos : 0 < p := by dsimp [p]; positivity
  have hTval : T = (n : ℝ) * p := by
    calc
      T = r * (r⁻¹ * T) := by field_simp
      _ = r * ((n : ℝ) * (2 * Real.pi)) := by rw [hphase]
      _ = (n : ℝ) * p := by dsimp [p]; ring
  have hpLe : p ≤ T := by
    rw [hTval]
    simpa using mul_le_mul_of_nonneg_right hnOne hpPos.le
  have hperiod : T = p := by
    by_contra hne
    have hpLt : p < T := lt_of_le_of_ne hpLe (Ne.symm hne)
    have hpp : p ∈ Icc 0 T := ⟨hpPos.le, hpLe⟩
    have hh := hsol p hpp
    have harg : r⁻¹ * p = 2 * Real.pi := by dsimp [p]; field_simp
    rw [harg] at hh
    have hfp : f p = f 0 := by simpa using hh
    have hγp : γ p = γ 0 := sub_left_inj.mp hfp
    have hz := hinj ⟨hpPos.le, hpLt⟩ ⟨le_rfl, hT⟩ hγp
    exact hpPos.ne' hz
  have hb := circle_positive_tangent hT hApos hr hC hp hunit hnorm hA
  have hint : (∫ t in (0 : ℝ)..T, boundaryIntegrand (fun t => γ t - z) v t) = r * T := by
    calc
      _ = ∫ _t in (0 : ℝ)..T, r := intervalIntegral.integral_congr
        (fun t ht => hb t (by simpa [uIcc_of_le hT.le] using ht))
      _ = r * T := by simp; ring
  rw [GreenAreaBridge.translation_invariance T γ v hT.le hC hp z] at hint
  have hAvalue : 2 * A = r * T := by linarith only [hA, hint]
  calc
    4 * Real.pi * A = (2 * Real.pi * r) * T := by linear_combination 2 * Real.pi * hAvalue
    _ = T ^ 2 := by change p * T = T ^ 2; rw [← hperiod]; ring

/-- The planar isoperimetric inequality and its complete image-based
circle equality case for every regular C¹ circle embedding. -/
theorem isoperimetric_inequality : Statement := by
  intro c hc
  obtain ⟨Ω, E, T, γ, v, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf,
    hcl, hboundary, hpos, hfin, harea, hparam, horient, hgreen, hA, htrans⟩ :=
    GreenAreaBridge.green_area_bridge c hc
  refine ⟨Ω, E, T, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf,
    hcl, hboundary, hpos, hfin, harea, hparam.1, hparam.2.1,
    unit_speed_area_bound hparam.1 hparam.2.2.1 hparam.2.2.2.1 hparam.2.2.2.2.2.2.2 hA,
    ?_⟩
  exact ⟨equality_implies_circle hparam hA,
    circle_implies_equality hparam harea hA⟩

end VariationalNotes.Classical.IsoperimetricInequality
