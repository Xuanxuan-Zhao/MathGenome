import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.IntervalCharacteristicInversion
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.SineIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The interval formula of paper.tex:2474–2482 and 2508–2528.
Finite Fubini reduces the cutoff to the bounded sine primitive. Its positive
limit is MathGenome's ordinary sine-integral theorem, its negative limit follows
by symmetry, and filter dominated convergence retains both half endpoint masses.
Compare Durrett, Probability: Theory and Examples, fifth edition, Theorem 3.3.11,
pp. 128–129 (the author's public PDF is recorded in research/).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace ProbabilityFoundations.Ch07

theorem intervalInversionQuotient_formula :
    Specs.ProbabilityFoundations.Ch07.IntervalCharacteristicInversion.QuotientFormula := by
  intro a b t ht
  rw [intervalInversionQuotient, integral_exp_mul_complex (neg_ne_zero.mpr
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht)))]
  simp only [neg_mul, div_neg]
  ring

theorem intervalInversionQuotient_zero :
    Specs.ProbabilityFoundations.Ch07.IntervalCharacteristicInversion.QuotientAtZero := by
  intro a b
  simp [intervalInversionQuotient]

lemma norm_exp_imaginary (r : ℝ) : ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I r

theorem continuous_intervalInversionQuotient :
    Specs.ProbabilityFoundations.Ch07.IntervalCharacteristicInversion.QuotientContinuous := by
  intro a b
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => 1)
  · intro t; fun_prop
  · intro t; exact ae_of_all _ (fun y _ => by
      have he : -(Complex.I * (t : ℂ)) * (y : ℂ) = ((-t*y : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [he, norm_exp_imaginary])
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun y _ => by fun_prop)

theorem intervalInversion_finiteCutoff_integrable :
    Specs.ProbabilityFoundations.Ch07.IntervalCharacteristicInversion.FiniteCutoffIntegrable := by
  intro μ _ a b T
  exact ((continuous_intervalInversionQuotient a b).mul (continuous_charFun (μ := μ))).intervalIntegrable _ _

/-- Oriented sine primitive, with the continuous sinc value at the origin. -/
def sinePrimitive (u : ℝ) : ℝ := ∫ v in 0..u, Real.sinc v

lemma continuous_sinePrimitive : Continuous sinePrimitive :=
  intervalIntegral.continuous_primitive (fun a b => Real.continuous_sinc.intervalIntegrable a b) 0

lemma tendsto_sinePrimitive_atTop : Tendsto sinePrimitive atTop (𝓝 (Real.pi / 2)) := by
  change Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, Real.sinc x) atTop (𝓝 (Real.pi / 2))
  have h := (D12Complex.SineIntegral.sine_integral 1 zero_lt_one).2.1
  simpa [sinePrimitive, D12Complex.SineIntegral.sineKernel,
    D12Complex.SineIntegral.Definitions.sineKernel] using h

lemma sinePrimitive_neg (u : ℝ) : sinePrimitive (-u) = -sinePrimitive u := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := u) Real.sinc
  change (∫ v in 0..(-u), Real.sinc v) = -(∫ v in 0..u, Real.sinc v)
  have he : (∫ v in 0..u, Real.sinc v) = ∫ v in (-u)..0, Real.sinc v := by
    simpa only [Real.sinc_neg, neg_zero] using h
  rw [intervalIntegral.integral_symm (-u) 0, ← he]

lemma sinePrimitive_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, |sinePrimitive u| ≤ C := by
  have ht : ∀ᶠ u : ℝ in atTop, |sinePrimitive u| < Real.pi / 2 + 1 := by
    apply (tendsto_sinePrimitive_atTop.abs).eventually (p := fun y => y < Real.pi / 2 + 1)
    apply gt_mem_nhds
    rw [abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 2)]
    linarith
  obtain ⟨R, hR⟩ := eventually_atTop.mp ht
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (continuous_sinePrimitive.abs.continuousOn (s := Icc 0 (max R 0)))
  let C := max (max M (Real.pi / 2 + 1)) 0
  have hpos : 0 ≤ C := le_max_right _ _
  have hb (u : ℝ) (hu : 0 ≤ u) : |sinePrimitive u| ≤ C := by
    by_cases hr : u ≤ max R 0
    · exact (hM (mem_image_of_mem _ ⟨hu, hr⟩)).trans
        ((le_max_left M _).trans (le_max_left _ _))
    · exact (hR u ((le_max_left R 0).trans (le_of_not_ge hr))).le.trans
        ((le_max_right M _).trans (le_max_left _ _))
  refine ⟨C, hpos, fun u => ?_⟩
  by_cases hu : 0 ≤ u
  · exact hb u hu
  · have h := hb (-u) (by linarith)
    simpa only [sinePrimitive_neg, abs_neg] using h

lemma tendsto_sinePrimitive_scaled (c : ℝ) :
    Tendsto (fun T : ℝ => sinePrimitive (T * c)) atTop
      (𝓝 (if 0 < c then Real.pi / 2 else if c < 0 then -(Real.pi / 2) else 0)) := by
  rcases lt_trichotomy 0 c with hc | hc | hc
  · simpa [hc, Function.comp_def] using tendsto_sinePrimitive_atTop.comp (tendsto_id.atTop_mul_const hc)
  · subst c; simp [sinePrimitive]
  · have hn := tendsto_sinePrimitive_atTop.comp (tendsto_id.atTop_mul_const (neg_pos.mpr hc))
    have he (T : ℝ) : sinePrimitive (T * c) = -sinePrimitive (T * (-c)) := by
      rw [mul_neg, sinePrimitive_neg]; simp
    simpa only [Function.comp_def, id_eq, he, ite_eq_right (not_lt.mpr hc.le), ite_eq_left hc] using hn.neg

lemma integral_cexp_symmetric (T c : ℝ) :
    (∫ t in -T..T, Complex.exp (((t*c : ℝ) : ℂ) * Complex.I)) =
      2 * (T : ℂ) * (Real.sinc (T*c) : ℂ) := by
  by_cases hc : c = 0
  · simp [hc, two_mul]
  rw [intervalIntegral.integral_comp_mul_right (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) hc]
  simp only [neg_mul, integral_exp_mul_I_eq_sinc, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hc]

lemma integral_scaled_sinc (a b T x : ℝ) :
    (∫ y in a..b, T * Real.sinc (T * (x-y))) =
      sinePrimitive (T*(x-a)) - sinePrimitive (T*(x-b)) := by
  have hd (u : ℝ) : HasDerivAt sinePrimitive (Real.sinc u) u := by
    exact intervalIntegral.integral_hasDerivAt_right
      (Real.continuous_sinc.intervalIntegrable 0 u)
      (Real.continuous_sinc.stronglyMeasurableAtFilter _ _)
      Real.continuous_sinc.continuousAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := fun y => -sinePrimitive (T*(x-y)))
    (f' := fun y => T * Real.sinc (T*(x-y)))
    (fun y _ => by
      have hg : HasDerivAt (fun z : ℝ => T*(x-z)) (-T) y := by
        simpa using (((hasDerivAt_const y x).sub (hasDerivAt_id y)).const_mul T)
      simpa only [Function.comp_def, Pi.neg_apply, neg_mul_neg, mul_comm] using
        ((hd (T*(x-y))).neg.comp y hg))
    (by apply Continuous.intervalIntegrable; fun_prop)
  simpa only [neg_sub_neg] using he

lemma intervalInversionQuotient_norm_le (a b t : ℝ) :
    ‖intervalInversionQuotient a b t‖ ≤ |b-a| := by
  change ‖∫ y in a..b, Complex.exp (-(Complex.I * (t : ℂ)) * (y : ℂ))‖ ≤ _
  calc
    _ ≤ 1 * |b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun y _ => ?_)
    _ = _ := one_mul _
  have he : -(Complex.I * (t : ℂ)) * (y : ℂ) = ((-t*y : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, norm_exp_imaginary]

/-- Integrate the finite frequency window before the spatial window. -/
lemma integral_quotient_cexp (a b T x : ℝ) :
    (∫ t in -T..T, intervalInversionQuotient a b t *
      Complex.exp (((t*x : ℝ) : ℂ) * Complex.I)) =
    2 * ((sinePrimitive (T*(x-a)) - sinePrimitive (T*(x-b)) : ℝ) : ℂ) := by
  calc
    _ = ∫ t in -T..T, ∫ y in a..b,
        Complex.exp (((t*(x-y) : ℝ) : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [intervalInversionQuotient, ← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = ∫ y in a..b, ∫ t in -T..T,
        Complex.exp (((t*(x-y) : ℝ) : ℂ) * Complex.I) := by
      apply intervalIntegral_intervalIntegral_swap
      have hc : Continuous (fun p : ℝ × ℝ =>
          Complex.exp (((p.1*(x-p.2) : ℝ) : ℂ) * Complex.I)) := by fun_prop
      exact (hc.continuousOn.integrableOn_compact
        (isCompact_uIcc.prod isCompact_uIcc)).mono_set
        (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
    _ = ∫ y in a..b, 2 * (T : ℂ) * (Real.sinc (T*(x-y)) : ℂ) := by
      simp_rw [integral_cexp_symmetric]
    _ = 2 * ((∫ y in a..b, T * Real.sinc (T*(x-y)) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      push_cast
      ring
    _ = _ := by rw [integral_scaled_sinc]

/-- The bounded spatial kernel after integrating out frequency. -/
def intervalSineKernel (a b T x : ℝ) : ℝ :=
  (sinePrimitive (T*(x-a)) - sinePrimitive (T*(x-b))) / Real.pi

lemma continuous_intervalSineKernel (a b T : ℝ) : Continuous (intervalSineKernel a b T) := by
  unfold intervalSineKernel
  exact ((continuous_sinePrimitive.comp (continuous_const.mul (continuous_id.sub continuous_const))).sub
    (continuous_sinePrimitive.comp (continuous_const.mul (continuous_id.sub continuous_const)))).div_const _

lemma intervalInversionCutoff_eq_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b T : ℝ) :
    intervalInversionCutoff μ a b T = ∫ x, (intervalSineKernel a b T x : ℂ) ∂μ := by
  have : IsFiniteMeasure (volume.restrict (uIoc (-T) T)) :=
    ⟨by simp [Real.volume_uIoc]⟩
  have h_int : Integrable (Function.uncurry fun (t x : ℝ) =>
      intervalInversionQuotient a b t * Complex.exp (((t*x : ℝ) : ℂ) * Complex.I))
      ((volume.restrict (uIoc (-T) T)).prod μ) := by
    apply (integrable_const (|b-a| : ℝ)).mono'
    · apply Continuous.aestronglyMeasurable
      exact ((continuous_intervalInversionQuotient a b).comp continuous_fst).mul (by fun_prop)
    · exact ae_of_all _ (fun p => by
        dsimp only [Function.uncurry]
        rw [norm_mul, norm_exp_imaginary, mul_one]
        exact intervalInversionQuotient_norm_le a b p.1)
  calc
    _ = (2 * (Real.pi : ℂ))⁻¹ * ∫ x, ∫ t in -T..T,
        intervalInversionQuotient a b t * Complex.exp (((t*x : ℝ) : ℂ) * Complex.I) ∂volume ∂μ := by
      unfold intervalInversionCutoff
      congr 1
      rw [← intervalIntegral_integral_swap h_int]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [charFun_apply_real, ← integral_const_mul]
      congr 1
      ext x
      simp only [Complex.ofReal_mul]
    _ = ∫ x, (2 * (Real.pi : ℂ))⁻¹ *
        (2 * ((sinePrimitive (T*(x-a)) - sinePrimitive (T*(x-b)) : ℝ) : ℂ)) ∂μ := by
      simp_rw [integral_quotient_cexp]
      rw [integral_const_mul ((2 * (Real.pi : ℂ))⁻¹)]
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        dsimp only [intervalSineKernel]
        push_cast
        field_simp)

/-- Pointwise limit, with the two distinct endpoint values retained. -/
def intervalEndpointWeight (a b x : ℝ) : ℝ :=
  (Ioo a b).indicator (fun _ => 1) x +
    ({a} : Set ℝ).indicator (fun _ => 1/2) x +
    ({b} : Set ℝ).indicator (fun _ => 1/2) x

lemma tendsto_intervalSineKernel {a b : ℝ} (hab : a < b) (x : ℝ) :
    Tendsto (fun T => intervalSineKernel a b T x) atTop (𝓝 (intervalEndpointWeight a b x)) := by
  have ht := ((tendsto_sinePrimitive_scaled (x-a)).sub
    (tendsto_sinePrimitive_scaled (x-b))).div_const Real.pi
  change Tendsto (fun T => (sinePrimitive (T*(x-a)) - sinePrimitive (T*(x-b))) / Real.pi)
    atTop (𝓝 _) 
  convert ht using 1
  dsimp [intervalEndpointWeight]
  rcases lt_trichotomy x a with hxa | hxa | hax
  · simp [show ¬a < x by linarith, show x-a < 0 by linarith,
      show ¬0 < x-a by linarith, show x-b < 0 by linarith,
      show ¬0 < x-b by linarith, show x ≠ a from hxa.ne,
      show x ≠ b by linarith]
  · subst x
    simp [hab.ne, show a-b < 0 by linarith, show ¬0 < a-b by linarith]
    field_simp
  · rcases lt_trichotomy x b with hxb | hxb | hbx
    · simp [hax, hxb, hax.ne', hxb.ne, show 0 < x-a by linarith,
        show x-b < 0 by linarith, show ¬0 < x-b by linarith]
    · subst x
      simp [hab, hab.ne', show 0 < b-a by linarith]
      field_simp
    · simp [show ¬x < b by linarith, hax.ne', hbx.ne',
        show 0 < x-a by linarith, show 0 < x-b by linarith]

lemma intervalSineKernel_bounded : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a b T x : ℝ, |intervalSineKernel a b T x| ≤ C := by
  obtain ⟨C, hC, hb⟩ := sinePrimitive_bounded
  refine ⟨(C+C)/Real.pi, by positivity, fun a b T x => ?_⟩
  rw [intervalSineKernel, abs_div, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right
    ((abs_sub _ _).trans (add_le_add (hb _) (hb _))) Real.pi_pos.le

lemma integral_intervalEndpointWeight (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    (∫ x, intervalEndpointWeight a b x ∂μ) =
      μ.real (Ioo a b) + (1/2) * μ.real {a} + (1/2) * μ.real {b} := by
  have hi (s : Set ℝ) (hs : MeasurableSet s) (c : ℝ) :
      Integrable (s.indicator (fun _ => c)) μ := (integrable_const c).indicator hs
  have hi₁ := hi (Ioo a b) measurableSet_Ioo 1
  have hi₂ := hi {a} (measurableSet_singleton a) (1/2)
  have hi₃ := hi {b} (measurableSet_singleton b) (1/2)
  calc
    _ = (∫ x, (Ioo a b).indicator (fun _ => (1 : ℝ)) x ∂μ) +
        (∫ x, ({a} : Set ℝ).indicator (fun _ => (1/2 : ℝ)) x ∂μ) +
        (∫ x, ({b} : Set ℝ).indicator (fun _ => (1/2 : ℝ)) x ∂μ) := by
      exact (integral_add (hi₁.add hi₂) hi₃).trans
        (congrArg (fun y : ℝ => y + ∫ x, ({b} : Set ℝ).indicator (fun _ => (1/2 : ℝ)) x ∂μ)
          (integral_add hi₁ hi₂))
    _ = _ := by
      rw [integral_indicator_const _ measurableSet_Ioo,
        integral_indicator_const _ (measurableSet_singleton a),
        integral_indicator_const _ (measurableSet_singleton b)]
      simp only [smul_eq_mul, mul_one]
      ring

theorem characteristicFunction_interval_inversion :
    Specs.ProbabilityFoundations.Ch07.IntervalCharacteristicInversion.IntervalInversion := by
  intro μ _ a b hab
  obtain ⟨C, hC, hb⟩ := intervalSineKernel_bounded
  have ht : Tendsto (fun T => ∫ x, intervalSineKernel a b T x ∂μ) atTop
      (𝓝 (∫ x, intervalEndpointWeight a b x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · exact Eventually.of_forall (fun T => (continuous_intervalSineKernel a b T).aestronglyMeasurable)
    · exact Eventually.of_forall (fun T => ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs] using hb a b T x))
    · exact integrable_const C
    · exact ae_of_all _ (tendsto_intervalSineKernel hab)
  have htc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  rw [integral_intervalEndpointWeight] at htc
  have he (T : ℝ) : intervalInversionCutoff μ a b T =
      ((∫ x, intervalSineKernel a b T x ∂μ : ℝ) : ℂ) := by
    rw [intervalInversionCutoff_eq_integral]
    exact integral_complex_ofReal
  simpa only [Function.comp_def, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, ← he] using htc

end ProbabilityFoundations.Ch07
