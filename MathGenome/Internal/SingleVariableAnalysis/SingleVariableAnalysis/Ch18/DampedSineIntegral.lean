import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.UniformComparison
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ProperContinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Lagrange
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SingleVariableAnalysis.DampedSineIntegral
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Riemann Riemann.Improper ParameterIntegral
namespace Spec
export Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral
  (integrandValue integralValue)
end Spec

abbrev integrand := Spec.integrandValue
abbrev J := Spec.integralValue

/-- Newton--Leibniz for a continuous real integrand, directly from the
all-tagged Darboux limit and real mean-value tags. -/
theorem darboux_eq_sub_of_hasDerivAt {f F : ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v)
    (hF : ContinuousOn F (Icc u v))
    (hd : ∀ x ∈ Ioo u v, HasDerivAt F (f x) x)
    (hi : RealIntegrable f u v) : realIntegral f hi = F v - F u := by
  apply eq_of_forall_dist_le
  intro ε hε
  have hlim := (real_tagged_equivalence f huv hi.bounded (realIntegral f hi)).mp ⟨hi, rfl⟩
  obtain ⟨δ, hδ, hδlim⟩ := hlim ε hε
  obtain ⟨P, hP⟩ := exists_fine_partition huv δ hδ
  have hm (i : Fin P.n) : ∃ c ∈ Ioo (P.point i.castSucc) (P.point i.succ),
      F (P.point i.succ) - F (P.point i.castSucc) =
        f c * (P.point i.succ - P.point i.castSucc) := by
    have hp := P.strictMono (Fin.castSucc_lt_succ (i := i))
    have hsub : Icc (P.point i.castSucc) (P.point i.succ) ⊆ Icc u v :=
      cell_subset_interval P i
    obtain ⟨c, hc, he⟩ := lagrange_deriv F _ _ hp (hF.mono hsub)
      (fun x hx => (hd x ⟨(hsub ⟨le_rfl, hp.le⟩).1.trans_lt hx.1,
        hx.2.trans_le (hsub ⟨hp.le, le_rfl⟩).2⟩).differentiableAt)
    have hc' : c ∈ Ioo u v := ⟨(hsub ⟨le_rfl, hp.le⟩).1.trans_lt hc.1,
      hc.2.trans_le (hsub ⟨hp.le, le_rfl⟩).2⟩
    exact ⟨c, hc, by simpa only [(hd c hc').deriv] using he⟩
  choose c hc he using hm
  let ξ : Tagging P := fun i => ⟨c i, Ioo_subset_Icc_self (hc i)⟩
  have hsum : taggedSum P ξ f = F v - F u := by
    change (∑ i : Fin P.n, cellLength P i * f (c i)) = _
    calc
      _ = ∑ i : Fin P.n, (F (P.point i.succ) - F (P.point i.castSucc)) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [cellLength, S.lengthValue, mul_comm] using (he i).symm
      _ = F v - F u := by
        simpa only [P.first, P.last] using sum_cell_differences (fun i => F (P.point i))
  have h := hδlim P ξ hP
  change ‖taggedSum P ξ f - realIntegral f hi‖ < ε at h
  rw [hsum] at h
  simpa only [dist_eq_norm, norm_sub_rev] using h.le

/-- On continuous real functions the finite measure integral has exactly the
proper Darboux value. This bridge is proved here, not postulated. -/
theorem darboux_eq_intervalIntegral {f : ℝ → ℝ} (hf : Continuous f)
    {u v : ℝ} (huv : u ≤ v) (hi : RealIntegrable f u v) :
    realIntegral f hi = ∫ x in u..v, f x := by
  let F : ℝ → ℝ := fun y => ∫ x in u..y, f x
  have hd (x : ℝ) : HasDerivAt F (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
      hf.continuousAt
  have he := darboux_eq_sub_of_hasDerivAt huv
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x) hi
  simpa only [F, intervalIntegral.integral_same, sub_zero] using he

/-- Continuous, integrable half-line sections have the required improper
Darboux limit. Only this proved bridge is used to transfer measure formulas. -/
theorem darboux_right_of_integrableOn {f : ℝ → ℝ} (hf : Continuous f)
    (b : ℝ) (hi : IntegrableOn f (Ioi b)) :
    RightHasIntegral .real f b ⊤ ((∫ x in Ioi b, f x) : ℝ) := by
  have hr : RightRegular .real f b ⊤ := ⟨WithTop.coe_lt_top _, fun R =>
    real_integrable_of_continuousOn R.property.1.le hf.continuousOn⟩
  refine ⟨hr, fun ε hε => ?_⟩
  have ht := intervalIntegral_tendsto_integral_Ioi b hi tendsto_id
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp ht) ε hε
  refine ⟨⟨max M (b+1), by linarith [le_max_right M (b+1)], WithTop.coe_lt_top _⟩,
    fun R hR => ?_⟩
  change dist (realIntegral f (hr.2 R)) _ < ε
  rw [darboux_eq_intervalIntegral hf R.property.1.le]
  exact hM R.val (le_of_lt ((le_max_left M (b+1)).trans_lt hR))

theorem continuous_extension :
    Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral.continuousExtension := by
  refine ⟨fun a => ?_, fun a => ?_, fun a x hx => ?_⟩
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul Real.continuous_sinc
  · simp [Spec.integrandValue]
  · simp only [Spec.integrandValue, Real.sinc_of_ne_zero hx]

theorem integrand_norm_le (a x : ℝ) : ‖integrand a x‖ ≤ Real.exp (-a*x) := by
  change |Real.exp (-a*x) * Real.sinc x| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one x)
    (Real.exp_pos (-a*x)).le

theorem sine_norm_le (a x : ℝ) : ‖Real.exp (-a*x) * Real.sin x‖ ≤ Real.exp (-a*x) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x)
    (Real.exp_pos (-a*x)).le

theorem integrand_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (integrand a) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).mono'
    (continuous_extension.1 a).aestronglyMeasurable
    (ae_of_all _ (integrand_norm_le a))

theorem sine_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => Real.exp (-a*x) * Real.sin x) (Ioi 0) := by
  apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).mono'
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-a*x) * Real.sin x)).aestronglyMeasurable
  · exact ae_of_all _ (sine_norm_le a)

theorem absolute_convergence :
    Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral.absoluteConvergence := by
  intro a ha
  exact ⟨darboux_right_of_integrableOn (continuous_extension.1 a) 0 (integrand_integrable ha),
    ⟨_, darboux_right_of_integrableOn (continuous_extension.1 a).norm 0
      (integrand_integrable ha).norm⟩⟩

/-- The elementary exponential majorant, including its Darboux value. -/
theorem exponential_integral {a : ℝ} (ha : 0 < a) :
    RightHasIntegral .real (fun x => Real.exp (-a*x)) 0 ⊤ (1/a) := by
  have h := darboux_right_of_integrableOn
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (-a*x))) 0
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0)
  simpa only [integral_exp_mul_Ioi (neg_neg_of_pos ha), mul_zero, Real.exp_zero,
    neg_div_neg_eq] using h

theorem integral_bound :
    Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral.integralBound := by
  intro a ha
  have h := right_hasIntegral_norm_le_majorant .real (integrand a)
    (fun x => Real.exp (-a*x)) (absolute_convergence a ha).1 (exponential_integral ha)
    (fun x _ _ => integrand_norm_le a x)
  exact h

/-- The primitive used in the paper is checked by differentiation. -/
theorem sine_primitive (a x : ℝ) :
    HasDerivAt (fun y => Real.exp (-a*y) * (-a * Real.sin y - Real.cos y) / (1+a^2))
      (Real.exp (-a*x) * Real.sin x) x := by
  have hn : 1+a^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((((hasDerivAt_id x).const_mul (-a)).exp).mul
    (((Real.hasDerivAt_sin x).const_mul (-a)).sub (Real.hasDerivAt_cos x))).div_const (1+a^2)
  convert! h using 1
  dsimp
  field_simp [hn]
  ring

theorem exp_decay {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.exp (-a*x)) atTop (𝓝 0) := by
  simpa only [neg_mul, Function.comp_def, id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop ha)

theorem sine_measure_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-a*x) * Real.sin x) = 1/(1+a^2) := by
  have hp : 0 < 1+a^2 := by positivity
  have hb (x : ℝ) : ‖-a * Real.sin x - Real.cos x‖ ≤ |a|+1 := by
    calc
      _ ≤ ‖-a * Real.sin x‖ + ‖Real.cos x‖ := norm_sub_le _ _
      _ ≤ |a| * 1 + 1 := add_le_add
        (by rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) (abs_nonneg a))
        (Real.abs_cos_le_one x)
      _ = _ := by ring
  have ht : Tendsto (fun x => Real.exp (-a*x) * (-a * Real.sin x - Real.cos x) / (1+a^2))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun x => Real.exp (-a*x) * (|a|+1) / (1+a^2))
    · intro x
      rw [norm_div, norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs (1+a^2), abs_of_pos hp]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb x) (Real.exp_pos _).le) hp.le
    · simpa using ((exp_decay ha).mul_const (|a|+1)).div_const (1+a^2)
  have hv := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x (_ : x ∈ Ici (0 : ℝ)) => sine_primitive a x) (sine_integrable ha) ht
  simpa only [mul_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero, mul_one,
    sub_zero, zero_sub, neg_div, neg_neg, one_mul] using hv

theorem exponential_sine_integral :
    Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral.exponentialSineIntegral := by
  intro a ha
  simpa only [sine_measure_integral ha] using darboux_right_of_integrableOn
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (-a*x) * Real.sin x)) 0
    (sine_integrable ha)

/-- The parameter derivative includes x=0, where the cancellation is removable. -/
theorem parameter_derivative (a x : ℝ) :
    HasDerivAt (fun b => integrand b x) (-Real.exp (-a*x) * Real.sin x) a := by
  have h := (((hasDerivAt_id a).const_mul (-x)).exp).mul_const (Real.sinc x)
  convert h using 1
  · funext b
    dsimp [integrand, Spec.integrandValue]
    congr 2; ring
  · by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]
      simp only [id_eq]
      rw [show -x * a = -a * x by ring]
      field_simp

theorem derivative_formula :
    Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral.derivativeFormula := by
  intro a ha
  have hm : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (integrand b)
      (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall (fun b => (continuous_extension.1 b).aestronglyMeasurable)
  have hdm : AEStronglyMeasurable (fun x => -Real.exp (-a*x) * Real.sin x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Continuous (fun x : ℝ => -Real.exp (-a*x) * Real.sin x)).aestronglyMeasurable
  have hb : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ b ∈ Ioi (a/2), ‖-Real.exp (-b*x) * Real.sin x‖ ≤ Real.exp (-(a/2)*x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro b hb
    calc
      _ = ‖Real.exp (-b*x) * Real.sin x‖ := by rw [neg_mul, norm_neg]
      _ ≤ Real.exp (-b*x) := sine_norm_le b x
      _ ≤ Real.exp (-(a/2)*x) := Real.exp_le_exp.mpr (by nlinarith [mem_Ioi.mp hx, mem_Ioi.mp hb])
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (isOpen_Ioi.mem_nhds (show a/2 < a by linarith)) hm (integrand_integrable ha) hdm hb
    (integrableOn_exp_mul_Ioi (show -(a/2) < 0 by linarith) 0)
    (ae_of_all _ (fun x b _ => parameter_derivative b x))
  have he : (∫ x in Ioi (0 : ℝ), -Real.exp (-a*x) * Real.sin x) = -1/(1+a^2) := by
    rw [show (fun x => -Real.exp (-a*x) * Real.sin x) =
      (fun x => -(Real.exp (-a*x) * Real.sin x)) by funext x; ring, integral_neg,
      sine_measure_integral ha]
    ring
  convert! hd.2 using 1
  exact he.symm

/-- Uniform derivative tails on a ≥ α. The common exponential majorant
controls all parameters with one truncation threshold. -/
theorem uniform_derivative_tails :
    Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral.uniformDerivativeTails := by
  intro α hα
  let f : ℝ → Ici α → ℝ := fun x a => -Real.exp (-a.val*x) * Real.sin x
  have hc (a : Ici α) : Continuous (fun x => f x a) := by dsimp [f]; fun_prop
  have hr : RightFamilyRegular .real (Ici α) f 0 ⊤ :=
    ⟨WithTop.coe_lt_top _, fun a => ⟨WithTop.coe_lt_top _, fun R =>
      real_integrable_of_continuousOn R.property.1.le (hc a).continuousOn⟩⟩
  have hdom : ∀ x : ℝ, 0 ≤ x → (x : WithTop ℝ) < ⊤ → ∀ a : Ici α,
      ‖f x a‖ ≤ Real.exp (-α*x) := by
    intro x hx _ a
    calc
      _ = ‖Real.exp (-a.val*x) * Real.sin x‖ := by simp only [f, neg_mul, norm_neg]
      _ ≤ Real.exp (-a.val*x) := sine_norm_le a.val x
      _ ≤ Real.exp (-α*x) := Real.exp_le_exp.mpr (by
        simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right a.property hx))
  obtain ⟨F, hF⟩ := right_uniform_converges_of_majorant .real (Ici α) f
    (fun x => Real.exp (-α*x)) le_rfl hr ⟨_, exponential_integral hα⟩ hdom
  have hpt (a : Ici α) : RightHasIntegral .real (fun x => f x a) 0 ⊤
      (-1/(1+a.val^2)) := by
    have hi : IntegrableOn (fun x => f x a) (Ioi 0) := by
      convert! (sine_integrable (hα.trans_le a.property)).neg using 1
      funext x
      dsimp only [f, Pi.neg_apply]
      ring
    have h := darboux_right_of_integrableOn (hc a) 0 hi
    have he : ((∫ x in Ioi (0 : ℝ), f x a) : ℝ) = -1/(1+a.val^2) := by
      dsimp [f]
      rw [show (fun x => -Real.exp (-a.val*x) * Real.sin x) =
        (fun x => -(Real.exp (-a.val*x) * Real.sin x)) by funext x; ring,
        integral_neg, sine_measure_integral (hα.trans_le a.property)]
      ring
    rwa [he] at h
  have he : F = (fun a : Ici α => -1/(1+a.val^2)) := by
    funext a
    exact right_unique .real (fun x => f x a) 0 ⊤ _ _
      (right_uniform_pointwise .real (Ici α) f 0 ⊤ F hF a) (hpt a)
  simpa only [he, f] using hF

theorem integral_tendsto_zero : Tendsto J atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    exact integral_bound a ha
  · convert (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)) using 1
    funext a
    exact one_div a

/-- Equal derivatives on the positive interval leave one constant. Both
functions tend to zero at +∞, fixing that constant. -/
theorem evaluation : Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral.evaluation := by
  let H : ℝ → ℝ := fun a => J a - (Real.pi/2 - Real.arctan a)
  have hd (a : ℝ) (ha : a ∈ Ioi (0 : ℝ)) : HasDerivAt H 0 a := by
    have hg := (Real.hasDerivAt_arctan a).const_sub (Real.pi/2)
    convert! (derivative_formula a ha).sub hg using 1
    simp only [neg_div, sub_neg_eq_add]
    ring
  have hconst : ∀ a ∈ Ioi (0 : ℝ), ∀ b ∈ Ioi (0 : ℝ), H a = H b := by
    intro a ha b hb
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hd x hx).deriv) ha hb
  have ht : Tendsto H atTop (𝓝 0) := by
    have hg : Tendsto (fun a => Real.pi/2 - Real.arctan a) atTop (𝓝 0) := by
      simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.pi/2) atTop (𝓝 (Real.pi/2))).sub
        (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds)
    simpa only [H, sub_zero] using integral_tendsto_zero.sub hg
  intro a ha
  have hlim : Tendsto H atTop (𝓝 (H a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    exact hconst a ha b hb
  have hz : H a = 0 := tendsto_nhds_unique hlim ht
  have he : J a = Real.pi/2 - Real.arctan a := sub_eq_zero.mp hz
  simpa only [one_div, Real.arctan_inv_of_pos ha] using he

end SingleVariableAnalysis.DampedSineIntegral
