import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.LinearGrowthNonattainment
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Spaces
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import MathGenome.Internal.FourierSobolev.P102.U4.ACL
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set MeasureTheory Filter
open scoped Topology
namespace VariationalNotes.Sobolev.LinearGrowth

theorem convex_gradient : Expected.ConvexGradient := by
  intro x hx
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ r s hr hs _
  have h := abs_add_le (r * a) (s * b)
  rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hs] at h
  have hc : 0 ≤ 1 + x := by linarith [hx.1]
  dsimp [integrand]
  nlinarith [mul_le_mul_of_nonneg_left h hc]

theorem linear_growth : Expected.PointwiseGrowth := by
  intro x hx z
  dsimp [integrand]
  constructor <;> nlinarith [abs_nonneg z, hx.1, hx.2]

lemma abs_deriv_integrable {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1) :
    IntervalIntegrable (fun x => |deriv f x|) volume 0 1 :=
  hf.intervalIntegrable_deriv.abs

lemma weighted_deriv_integrable {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1) :
    IntervalIntegrable (fun x => x * |deriv f x|) volume 0 1 :=
  (abs_deriv_integrable hf).continuousOn_mul continuousOn_id

lemma energy_integrable {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1) :
    IntervalIntegrable (fun x => integrand x (deriv f x)) volume 0 1 :=
  (abs_deriv_integrable hf).continuousOn_mul (by fun_prop)

lemma energy_decomposition {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1) :
    energy f = (∫ x in (0 : ℝ)..1, |deriv f x|) +
      ∫ x in (0 : ℝ)..1, x * |deriv f x| := by
  unfold energy integrand
  simp_rw [add_mul, one_mul]
  exact intervalIntegral.integral_add (abs_deriv_integrable hf) (weighted_deriv_integrable hf)

lemma total_derivative {f : ℝ → ℝ} (hf : Admissible f) :
    ∫ x in (0 : ℝ)..1, deriv f x = 1 := by
  simpa [hf.2.1, hf.2.2] using hf.1.integral_deriv_eq_sub

lemma variation_ge_one {f : ℝ → ℝ} (hf : Admissible f) :
    1 ≤ ∫ x in (0 : ℝ)..1, |deriv f x| := by
  have h := intervalIntegral.norm_integral_le_integral_norm (f := deriv f)
    (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  simpa [total_derivative hf, Real.norm_eq_abs] using h

lemma weighted_variation_pos {f : ℝ → ℝ} (hf : Admissible f) :
    0 < ∫ x in (0 : ℝ)..1, x * |deriv f x| := by
  have hn : 0 ≤ ∫ x in (0 : ℝ)..1, x * |deriv f x| :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x hx => mul_nonneg hx.1 (abs_nonneg _))
  apply lt_of_le_of_ne hn
  intro he
  have hz := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
    (by norm_num : (0 : ℝ) ≤ 1) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg hx.1.le (abs_nonneg (deriv f x)))
    (weighted_deriv_integrable hf.1)).mp he.symm
  have hd : deriv f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 := by
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioc] with x hx hxi
    exact abs_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (ne_of_gt hxi.1))
  have hi : ∫ x in (0 : ℝ)..1, deriv f x = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa using integral_congr_ae hd
  linarith [total_derivative hf]

theorem strict_bound : Expected.StrictBound := by
  intro f hf
  rw [energy_decomposition hf.1]
  linarith [variation_ge_one hf, weighted_variation_pos hf]

lemma pointwise_bound {f : ℝ → ℝ} (hf : Admissible f) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    |f x| ≤ ∫ t in (0 : ℝ)..1, |deriv f t| := by
  have hs : Set.uIcc 0 x ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hx.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hx.2
  have hi := hf.1.mono hs
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (f := deriv f) (μ := volume) hx.1
  rw [hi.integral_deriv_eq_sub, hf.2.1, sub_zero, Real.norm_eq_abs] at hnorm
  simp_rw [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  apply intervalIntegral.integral_mono_interval (by rfl) hx.1 hx.2
  · filter_upwards with t
    exact abs_nonneg _
  · exact abs_deriv_integrable hf.1

theorem coercivity : Expected.Coercivity := by
  intro f hf
  have hfi : IntervalIntegrable (fun x => |f x|) volume 0 1 :=
    hf.1.continuousOn.abs.intervalIntegrable
  have hu : (∫ x in (0 : ℝ)..1, |f x|) ≤ ∫ x in (0 : ℝ)..1, |deriv f x| := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hfi (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => ∫ x in (0 : ℝ)..1, |deriv f x|) volume 0 1)
      (fun x hx => pointwise_bound hf hx)
    simpa using h
  have hv : (∫ x in (0 : ℝ)..1, |deriv f x|) ≤ energy f := by
    rw [energy_decomposition hf.1]
    linarith [weighted_variation_pos hf]
  dsimp [sourceNorm]
  linarith

theorem ramp_admissible : Expected.RampAdmissible := by
  intro n hn
  refine ⟨?_, ?_, ?_⟩
  · have h : LipschitzWith ‖(n : ℝ)‖₊ (fun x : ℝ => (n : ℝ) * x) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        simp only [Real.dist_eq, ← mul_sub, abs_mul, coe_nnnorm, Real.norm_eq_abs]
        exact le_rfl
    exact (h.min_const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  · simp [ramp]
  · simp only [ramp, mul_one, min_eq_right_iff]
    exact_mod_cast hn

lemma ramp_derivative_left {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x < 1 / (n : ℝ)) :
    deriv (ramp n) x = (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : (n : ℝ) * x < 1 := by nlinarith [(lt_div_iff₀ hn').mp hx]
  have he : ramp n =ᶠ[𝓝 x] (fun y : ℝ => (n : ℝ) * y) := by
    filter_upwards [((continuous_const.mul continuous_id).isOpen_preimage
      (Iio 1) isOpen_Iio).mem_nhds hlt] with y hy
    exact min_eq_left hy.le
  rw [he.deriv_eq]
  simp

lemma ramp_derivative_right {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 1 / (n : ℝ) < x) :
    deriv (ramp n) x = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : 1 < (n : ℝ) * x := by nlinarith [(div_lt_iff₀ hn').mp hx]
  have he : ramp n =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [((continuous_const.mul continuous_id).isOpen_preimage
      (Ioi 1) isOpen_Ioi).mem_nhds hlt] with y hy
    exact min_eq_right hy.le
  rw [he.deriv_eq]
  simp

theorem ramp_energy : Expected.RampEnergy := by
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < 1 / (n : ℝ) := by positivity
  have ha1 : 1 / (n : ℝ) ≤ 1 := by
    apply (div_le_one hn').mpr
    exact_mod_cast hn
  have hf := (ramp_admissible n hn).1
  have he := energy_integrable hf
  have hl : (∫ x in (0 : ℝ)..(1 / (n : ℝ)), integrand x (deriv (ramp n) x)) =
      ∫ x in (0 : ℝ)..(1 / (n : ℝ)), (1 + x) * (n : ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ha.le
    intro x hx
    dsimp only [integrand]
    rw [ramp_derivative_left hn hx.2, abs_of_pos hn']
  have hr : (∫ x in (1 / (n : ℝ))..1, integrand x (deriv (ramp n) x)) = 0 := by
    trans ∫ x in (1 / (n : ℝ))..1, (0 : ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le ha1
      intro x hx
      simp [integrand, ramp_derivative_right hn hx.1]
    · simp
  have hleft : IntervalIntegrable (fun x => integrand x (deriv (ramp n) x))
      volume 0 (1 / (n : ℝ)) := he.mono_set (by
    rw [uIcc_of_le ha.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl ha1)
  have hright : IntervalIntegrable (fun x => integrand x (deriv (ramp n) x))
      volume (1 / (n : ℝ)) 1 := he.mono_set (by
    rw [uIcc_of_le ha1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc ha.le le_rfl)
  unfold energy
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hl, hr, add_zero]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one,
    integral_id, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  field_simp [ne_of_gt hn']

theorem infimum : Expected.Infimum := by
  constructor
  · rintro y ⟨f, hf, rfl⟩
    exact (strict_bound f hf).le
  · intro b hb
    by_contra h
    have hδ : 0 < b - 1 := by linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    have hn' : 0 < n + 1 := Nat.succ_pos n
    have hi := hb (mem_image_of_mem energy (ramp_admissible (n + 1) hn'))
    rw [ramp_energy (n + 1) hn'] at hi
    have hnp : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hd : 1 / (2 * ((n + 1 : ℕ) : ℝ)) ≤ 1 / ((n : ℝ) + 1) := by
      rw [Nat.cast_add, Nat.cast_one]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    linarith

theorem nonattainment : Expected.Nonattainment := by
  rintro ⟨f, hf, hmin⟩
  have hm : energy f ∈ lowerBounds (energy '' {g | Admissible g}) := by
    rintro y ⟨g, hg, rfl⟩
    exact hmin g hg
  have := infimum.2 hm
  linarith [strict_bound f hf]

/-- The volume-preserving identification of the one-dimensional domain with ℝ. -/
def realEquiv : Domain 1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
    (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ))

@[simp] lemma realEquiv_apply (x : Domain 1) : realEquiv x = x 0 := rfl
@[simp] lemma realEquiv_symm_coordinate (x : Domain 1) : realEquiv.symm (x 0) = x :=
  realEquiv.symm_apply_apply x

@[simp] lemma realEquiv_symm_apply (t : ℝ) (i : Fin 1) : realEquiv.symm t i = t := rfl

lemma realEquiv_measurePreserving : MeasurePreserving realEquiv volume volume :=
  (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).comp
    ((PiLp.volume_preserving_toLp (Fin 1)).symm
      (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)))

lemma coordinate_measurePreserving : MeasurePreserving realEquiv
    (domainMeasure intervalDomain) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  realEquiv_measurePreserving.restrict_preimage measurableSet_Ioo

lemma line_measurePreserving : MeasurePreserving realEquiv.symm
    (volume.restrict (Ioo (0 : ℝ) 1)) (domainMeasure intervalDomain) :=
  coordinate_measurePreserving.symm realEquiv

lemma acl_line_eq (t : ℝ) : P102.U4.ACL.line (0 : Fin 1) 0 t = realEquiv.symm t := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [P102.U4.ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine]

lemma acl_fiber_eq : P102.U4.ACL.fiber intervalDomain (0 : Fin 1) 0 = Ioo (0 : ℝ) 1 := by
  ext t
  simp [P102.U4.ACL.fiber, acl_line_eq, intervalDomain]

lemma scalar_integrable (u : P102.U4.DomainLp ℝ intervalDomain one.ennreal) :
    Integrable u (domainMeasure intervalDomain) := by
  apply memLp_one_iff_integrable.mp
  simpa [one, Exponent.ennreal] using Lp.memLp u

lemma scalar_line_integrable (u : P102.U4.DomainLp ℝ intervalDomain one.ennreal) :
    IntegrableOn (fun t => u (realEquiv.symm t)) (Ioo (0 : ℝ) 1) :=
  line_measurePreserving.integrable_comp_of_integrable (scalar_integrable u)

/-- Integrable derivatives extend a locally AC representative to both endpoints. -/
lemma extend_locallyAC {H g : ℝ → ℝ}
    (hH : P102.U4.ACL.LocallyAC H (Ioo (0 : ℝ) 1))
    (hg : IntervalIntegrable g volume 0 1)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), HasDerivAt H (g t) t) :
    ∃ G : ℝ → ℝ, AbsolutelyContinuousOnInterval G 0 1 ∧
      EqOn H G (Ioo (0 : ℝ) 1) ∧
      deriv G =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g := by
  let c : ℝ := 1 / 2
  have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
  let P (t : ℝ) := ∫ s in (0 : ℝ)..t, g s
  let G (t : ℝ) := P t + (H c - P c)
  have hP : AbsolutelyContinuousOnInterval P 0 1 :=
    hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hG : AbsolutelyContinuousOnInterval G 0 1 :=
    hP.add ((LipschitzWith.const (H c - P c)).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hdg : deriv G =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hg.ae_hasDerivAt_integral] with t ht hti
    have ht' : t ∈ uIcc (0 : ℝ) 1 := by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨hti.1.le, hti.2.le⟩
    exact ((ht ht' 0 left_mem_uIcc).add_const (H c - P c)).deriv
  refine ⟨G, hG, ?_, hdg⟩
  intro x hx
  have hsub : uIcc c x ⊆ Ioo (0 : ℝ) 1 :=
    (convex_Ioo (0 : ℝ) 1).ordConnected.uIcc_subset hc hx
  have hcx := hH c x hsub
  have hi : ∫ t in c..x, g t = H x - H c := by
    rw [← hcx.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    have hd' := (ae_restrict_iff' measurableSet_Ioo).mp hd
    filter_upwards [hd'] with t ht hti
    exact (ht (hsub (uIoc_subset_uIcc hti))).deriv.symm
  have h0x : IntervalIntegrable g volume 0 x := hg.mono_set (by
    rw [uIcc_of_le hx.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hx.2.le)
  have h0c : IntervalIntegrable g volume 0 c := hg.mono_set (by
    rw [uIcc_of_le hc.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hc.2.le)
  have hi' := intervalIntegral.integral_interval_sub_left h0x h0c
  dsimp [G, P]
  linarith

theorem representative_existence : Expected.RepresentativeExistence := by
  intro w
  let u := coordinateLp intervalDomain one (0 : Fin 1) (value intervalDomain 1 one w)
  let v := coordinateLp intervalDomain one ((0 : Fin 1), (0 : Fin 1))
    (gradient intervalDomain 1 one w)
  have hu : LocallyIntegrableOn (u : Domain 1 → ℝ) intervalDomain volume :=
    (show IntegrableOn (u : Domain 1 → ℝ) intervalDomain volume from
      scalar_integrable u).locallyIntegrableOn
  have hv : LocallyIntegrableOn (v : Domain 1 → ℝ) intervalDomain volume :=
    (show IntegrableOn (v : Domain 1 → ℝ) intervalDomain volume from
      scalar_integrable v).locallyIntegrableOn
  have hweak := distribution_derivative intervalDomain one w (0 : Fin 1) (0 : Fin 1)
  obtain ⟨F, hF, hAC, hD⟩ := (P102.U4.acl_dimensionOne ℝ intervalDomain u v hu hv).mp hweak
  simp only [acl_fiber_eq, acl_line_eq] at hAC hD
  let H (t : ℝ) := F (realEquiv.symm t)
  let g (t : ℝ) := v (realEquiv.symm t)
  have hgcc : IntegrableOn g (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mpr (scalar_line_integrable v)
  have hg : IntervalIntegrable g volume 0 1 := hgcc.intervalIntegrable
  obtain ⟨G, hG, hHG, hdG⟩ := extend_locallyAC hAC hg hD
  refine ⟨G, hG, ?_, ?_⟩
  · filter_upwards [hF, ae_restrict_mem intervalDomain.isOpen.measurableSet] with x hx hxi
    have hix : x 0 ∈ Ioo (0 : ℝ) 1 := hxi
    have he := hHG hix
    simpa only [H, realEquiv_symm_coordinate] using hx.trans (by simpa [realEquiv_symm_coordinate] using he)
  · have hdGa := coordinate_measurePreserving.quasiMeasurePreserving.ae hdG
    filter_upwards [hdGa] with x hx
    simpa only [realEquiv_apply, g, realEquiv_symm_coordinate] using hx.symm

theorem representative_lift : Expected.RepresentativeLift := by
  intro f hf
  have hfi : IntegrableOn f (Ioo (0 : ℝ) 1) :=
    hf.continuousOn.intervalIntegrable.1.mono_set Ioo_subset_Ioc_self
  have hdi : IntegrableOn (deriv f) (Ioo (0 : ℝ) 1) :=
    (hf.intervalIntegrable_deriv.1).mono_set Ioo_subset_Ioc_self
  have huf : MemLp (fun x : Domain 1 => f (x 0)) one.ennreal
      (domainMeasure intervalDomain) := by
    have hm := (memLp_one_iff_integrable.mpr hfi).comp_measurePreserving coordinate_measurePreserving
    simpa [one, Exponent.ennreal, Function.comp_def] using hm
  have hvf : MemLp (fun x : Domain 1 => deriv f (x 0)) one.ennreal
      (domainMeasure intervalDomain) := by
    have hm := (memLp_one_iff_integrable.mpr hdi).comp_measurePreserving coordinate_measurePreserving
    simpa [one, Exponent.ennreal, Function.comp_def] using hm
  let u := huf.toLp (fun x : Domain 1 => f (x 0))
  let v := hvf.toLp (fun x : Domain 1 => deriv f (x 0))
  have hu : (u : Domain 1 → ℝ) =ᵐ[domainMeasure intervalDomain] (fun x => f (x 0)) :=
    huf.coeFn_toLp
  have hv : (v : Domain 1 → ℝ) =ᵐ[domainMeasure intervalDomain] (fun x => deriv f (x 0)) :=
    hvf.coeFn_toLp
  have hui : LocallyIntegrableOn (u : Domain 1 → ℝ) intervalDomain volume :=
    (show IntegrableOn (u : Domain 1 → ℝ) intervalDomain volume from
      scalar_integrable u).locallyIntegrableOn
  have hvi : LocallyIntegrableOn (v : Domain 1 → ℝ) intervalDomain volume :=
    (show IntegrableOn (v : Domain 1 → ℝ) intervalDomain volume from
      scalar_integrable v).locallyIntegrableOn
  have heq : P102.U4.distributionPartial {(0 : Fin 1)} (P102.U4.regularDistribution intervalDomain u) =
      P102.U4.regularDistribution intervalDomain v := by
    apply (P102.U4.acl_dimensionOne ℝ intervalDomain u v hui hvi).mpr
    refine ⟨fun x => f (x 0), hu, ?_, ?_⟩
    · simp only [acl_fiber_eq, acl_line_eq, realEquiv_symm_apply]
      intro a b hab
      apply hf.mono
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hab.trans Ioo_subset_Icc_self
    · simp only [acl_fiber_eq, acl_line_eq, realEquiv_symm_apply]
      have hv' := line_measurePreserving.quasiMeasurePreserving.ae hv
      have hd : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), HasDerivAt f (deriv f t) t := by
        apply (ae_restrict_iff' measurableSet_Ioo).mpr
        filter_upwards [hf.ae_differentiableAt] with t ht hti
        apply (ht ?_).hasDerivAt
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact Ioo_subset_Icc_self hti
      filter_upwards [hd, hv'] with t ht hvt
      simpa only [realEquiv_symm_apply] using hvt.symm ▸ ht
  let U : ValueLp intervalDomain 1 one := assembleLp intervalDomain one (fun _ : Fin 1 => u)
  let V : GradientLp intervalDomain 1 one :=
    assembleLp intervalDomain one (fun _ : Fin 1 × Fin 1 => v)
  have hUV : WithLp.toLp one.ennreal (U, V) ∈ weakDerivativeGraph intervalDomain 1 one := by
    apply (mem_weakDerivativeGraph_iff intervalDomain one _).mpr
    intro i j
    change P102.U4.distributionPartial {j}
      (P102.U4.regularDistribution intervalDomain (coordinateLp intervalDomain one i U)) =
        P102.U4.regularDistribution intervalDomain (coordinateLp intervalDomain one (i,j) V)
    simp only [U, V, coordinate_assemble]
    have hj : j = 0 := Subsingleton.elim _ _
    simpa [hj] using heq
  let w : ScalarW11 := ⟨WithLp.toLp one.ennreal (U, V), hUV⟩
  refine ⟨w, ?_, ?_⟩
  · change coordinateLp intervalDomain one (0 : Fin 1) U =ᵐ[_] _
    rw [show coordinateLp intervalDomain one (0 : Fin 1) U = u from
      coordinate_assemble intervalDomain one 0 _]
    exact hu
  · change coordinateLp intervalDomain one ((0 : Fin 1), (0 : Fin 1)) V =ᵐ[_] _
    rw [show coordinateLp intervalDomain one ((0 : Fin 1), (0 : Fin 1)) V = v from
      coordinate_assemble intervalDomain one (0,0) _]
    exact hv

lemma scalar_value_norm (v : Vector 1) : ‖v‖ = |v 0| := by
  simp [EuclideanSpace.norm_eq, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

lemma scalar_gradient_norm (v : Gradient 1 1) : ‖v‖ = |v (0,0)| := by
  simp [EuclideanSpace.norm_eq, Real.norm_eq_abs, Fintype.sum_prod_type, Real.sqrt_sq_eq_abs]

lemma lp_one_norm {ι : Type*} [Fintype ι]
    (u : Lp (EuclideanSpace ℝ ι) one.ennreal (domainMeasure intervalDomain)) :
    ‖u‖ = ∫ x, ‖u x‖ ∂domainMeasure intervalDomain := by
  rw [Lp.norm_def]
  conv_lhs =>
    arg 1
    arg 2
    rw [show one.ennreal = 1 by norm_num [one, Exponent.ennreal]]
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable u)]
  exact (integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable u)).symm

lemma abs_coordinate_integral (f : ℝ → ℝ) :
    (∫ x : Domain 1, |f (x 0)| ∂domainMeasure intervalDomain) =
      ∫ t in (0 : ℝ)..1, |f t| := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  exact coordinate_measurePreserving.integral_comp realEquiv.measurableEmbedding (fun t => |f t|)

theorem norm_identification : Expected.NormIdentification := by
  intro w f _hf hrep
  have hu := coordinateLp_ae intervalDomain one (0 : Fin 1) (value intervalDomain 1 one w)
  have hv := coordinateLp_ae intervalDomain one ((0 : Fin 1), (0 : Fin 1))
    (gradient intervalDomain 1 one w)
  have hval : ‖value intervalDomain 1 one w‖ = ∫ t in (0 : ℝ)..1, |f t| := by
    rw [lp_one_norm, ← abs_coordinate_integral]
    apply integral_congr_ae
    filter_upwards [hu, hrep.1] with x hx hy
    rw [scalar_value_norm, ← hx, hy]
  have hgrad : ‖gradient intervalDomain 1 one w‖ = ∫ t in (0 : ℝ)..1, |deriv f t| := by
    rw [lp_one_norm, ← abs_coordinate_integral]
    apply integral_congr_ae
    filter_upwards [hv, hrep.2] with x hx hy
    rw [scalar_gradient_norm, ← hx, hy]
  rw [norm_eq intervalDomain one w]
  simp only [show one.real = 1 from rfl, Real.rpow_one, one_div, inv_one, hval, hgrad, sourceNorm]

theorem representative_uniqueness : Expected.RepresentativeUniqueness := by
  intro w f g hf hg hrf hrg
  have he := hrf.1.symm.trans hrg.1
  have he' := line_measurePreserving.quasiMeasurePreserving.ae he
  have hae : f =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] g := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [he'] with t ht
    simpa only [realEquiv_symm_apply] using ht
  apply Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hae
  · simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hf.continuousOn
  · simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hg.continuousOn

theorem energy_representation : Expected.EnergyRepresentation := by
  intro w f hrep
  have hd := line_measurePreserving.quasiMeasurePreserving.ae hrep.2
  unfold classEnergy energy
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [hd] with t ht
  exact congrArg (integrand t) ht

theorem class_coercivity : Expected.ClassCoercivity := by
  rintro w ⟨f, hf, hrep⟩
  rw [norm_identification w f hf.1 hrep, energy_representation w f hrep]
  exact coercivity f hf

theorem class_strict_bound : Expected.ClassStrictBound := by
  rintro w ⟨f, hf, hrep⟩
  rw [energy_representation w f hrep]
  exact strict_bound f hf

theorem class_ramp : Expected.ClassRamp := by
  intro n hn
  obtain ⟨w, hrep⟩ := representative_lift (ramp n) (ramp_admissible n hn).1
  exact ⟨w, ⟨ramp n, ramp_admissible n hn, hrep⟩, hrep,
    (energy_representation w (ramp n) hrep).trans (ramp_energy n hn)⟩

lemma energy_range_eq : classEnergy '' boundaryClass = energy '' {f | Admissible f} := by
  ext y
  constructor
  · rintro ⟨w, ⟨f, hf, hrep⟩, rfl⟩
    exact ⟨f, hf, (energy_representation w f hrep).symm⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨w, hrep⟩ := representative_lift f hf.1
    exact ⟨w, ⟨f, hf, hrep⟩, energy_representation w f hrep⟩

theorem class_infimum : Expected.ClassInfimum := by
  rw [Expected.ClassInfimum, energy_range_eq]
  exact infimum

theorem class_nonattainment : Expected.ClassNonattainment := by
  rintro ⟨w, hw, hmin⟩
  have hm : classEnergy w ∈ lowerBounds (classEnergy '' boundaryClass) := by
    rintro y ⟨v, hv, rfl⟩
    exact hmin v hv
  have := class_infimum.2 hm
  linarith [class_strict_bound w hw]

end VariationalNotes.Sobolev.LinearGrowth
