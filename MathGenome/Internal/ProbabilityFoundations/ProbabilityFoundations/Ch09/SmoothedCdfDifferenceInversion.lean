import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.SmoothedCdfDifferenceInversion
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.IntegrableCharacteristicDensity
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set Topology
open scoped FourierTransform RealInnerProductSpace

namespace ProbabilityFoundations.Ch09

lemma firstMoment_memLp {μ : Measure ℝ} (hμ : Integrable (fun x : ℝ => |x|) μ) :
    MemLp (id : ℝ → ℝ) 1 μ := by
  exact (memLp_one_iff_integrable).2 (hμ.mono' (by fun_prop) (by simp))

lemma characteristicDifferenceQuotient_continuous (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hν : Integrable (fun x : ℝ => |x|) ν) :
    Continuous (characteristicDifferenceQuotient μ ν) := by
  apply continuous_iff_continuousAt.2
  intro t
  by_cases ht : t = 0
  · subst t
    apply continuousAt_dslope_same.2
    exact ((contDiff_charFun (μ := μ) (n := 1) (by simpa using firstMoment_memLp hμ)).differentiable (by norm_num) 0).sub
      ((contDiff_charFun (μ := ν) (n := 1) (by simpa using firstMoment_memLp hν)).differentiable (by norm_num) 0)
  · exact (continuousAt_dslope_of_ne ht).2
      ((continuous_charFun (μ := μ)).sub (continuous_charFun (μ := ν))).continuousAt

lemma characteristicDifferenceQuotient_eq (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {t : ℝ} (ht : t ≠ 0) :
    characteristicDifferenceQuotient μ ν t = (charFun μ t - charFun ν t) / (t : ℂ) := by
  simp [characteristicDifferenceQuotient, dslope_of_ne _ ht, slope_def_module,
    charFun_zero, Complex.real_smul, div_eq_mul_inv, mul_comm]

lemma characteristicDifferenceQuotient_zero (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hν : Integrable (fun x : ℝ => |x|) ν) :
    characteristicDifferenceQuotient μ ν 0 =
      Complex.I * ((∫ x : ℝ, x ∂μ) - (∫ x : ℝ, x ∂ν) : ℝ) := by
  have hdμ := (contDiff_charFun (μ := μ) (n := 1) (by simpa using firstMoment_memLp hμ)).differentiable (by norm_num)
  have hdν := (contDiff_charFun (μ := ν) (n := 1) (by simpa using firstMoment_memLp hν)).differentiable (by norm_num)
  have hmμ := iteratedDeriv_charFun_zero (μ := μ) (n := 1) (by simpa using firstMoment_memLp hμ)
  have hmν := iteratedDeriv_charFun_zero (μ := ν) (n := 1) (by simpa using firstMoment_memLp hν)
  rw [characteristicDifferenceQuotient, dslope_same]
  rw [show (fun t => charFun μ t - charFun ν t) = charFun μ - charFun ν from rfl,
    deriv_sub (hdμ 0) (hdν 0)]
  simp only [iteratedDeriv_one, pow_one] at hmμ hmν
  rw [hmμ, hmν]
  push_cast
  ring

lemma smoothedCharacteristicQuotient_continuous (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    (T : ℝ) (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hν : Integrable (fun x : ℝ => |x|) ν) :
    Continuous (smoothedCharacteristicQuotient μ ν J T) := by
  exact (characteristicDifferenceQuotient_continuous μ ν hμ hν).mul
    (hJ.2.2.2.2.2.2.2.2.2.2.1.comp (by fun_prop))

lemma smoothedCharacteristicQuotient_eq (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : ℝ → ℝ) (T : ℝ) {t : ℝ} (ht : t ≠ 0) :
    smoothedCharacteristicQuotient μ ν J T t =
      smoothedCharacteristicDifference μ ν J T t / (t : ℂ) := by
  rw [smoothedCharacteristicQuotient, characteristicDifferenceQuotient_eq μ ν ht,
    smoothedCharacteristicDifference]
  ring

lemma smoothedCharacteristicQuotient_support (μ ν : Measure ℝ)
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    {T : ℝ} (hT : 0 < T) :
    Function.support (smoothedCharacteristicQuotient μ ν J T) ⊆ Icc (-T) T := by
  intro t ht
  by_contra h
  have ha : T < |t| := lt_of_not_ge (fun hh => h (abs_le.mp hh))
  have hc : charFun (smoothingMeasure J) (t / T) = 0 := by
    apply hJ.2.2.2.2.2.2.2.2.1
    rw [abs_div, abs_of_pos hT]
    exact (lt_div_iff₀ hT).2 (by simpa using ha)
  exact ht (by simp [smoothedCharacteristicQuotient, hc])

lemma smoothedCharacteristicQuotient_integrable (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    {T : ℝ} (hT : 0 < T) (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hν : Integrable (fun x : ℝ => |x|) ν) :
    Integrable (smoothedCharacteristicQuotient μ ν J T) := by
  apply (smoothedCharacteristicQuotient_continuous μ ν J hJ T hμ hν).integrable_of_hasCompactSupport
  exact HasCompactSupport.intro isCompact_Icc
    (fun t ht => Function.notMem_support.mp (fun h => ht (smoothedCharacteristicQuotient_support μ ν J hJ hT h)))

/-- Inverse Fourier integral in the manuscript's probability convention. -/
noncomputable def probabilityInverseIntegral (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) *
    ∫ t : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * f t

lemma norm_probabilityInverseKernel (t x : ℝ) :
    ‖Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))‖ = 1 := by
  simp [Complex.norm_exp]

lemma probabilityInverseKernel_integrable {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * f t) := by
  apply hf.norm.mono' ((by fun_prop : Continuous
    (fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)))).aestronglyMeasurable.mul hf.1)
  filter_upwards [] with t
  change ‖Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * f t‖ ≤ ‖f t‖
  rw [norm_mul, norm_probabilityInverseKernel, one_mul]

lemma probabilityInverseIntegral_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (probabilityInverseIntegral f) := by
  apply continuous_const.mul
  apply continuous_of_dominated
  · intro x
    exact (probabilityInverseKernel_integrable hf x).1
  · intro x
    exact ae_of_all _ fun t => by rw [norm_mul, norm_probabilityInverseKernel, one_mul]
  · exact hf.norm
  · filter_upwards [] with t
    fun_prop

lemma probabilityInverseIntegral_eq_fourier (f : ℝ → ℂ) (x : ℝ) :
    probabilityInverseIntegral f x =
      (1 / (2 * Real.pi) : ℝ) * 𝓕 f (x / (2 * Real.pi)) := by
  rw [probabilityInverseIntegral, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- Riemann--Lebesgue fixes the constant of the primitive at minus infinity. -/
lemma probabilityInverseIntegral_tendsto_atBot (f : ℝ → ℂ) :
    Tendsto (probabilityInverseIntegral f) atBot (𝓝 0) := by
  have hs : Tendsto (fun x : ℝ => x / (2 * Real.pi)) atBot atBot :=
    tendsto_id.atBot_div_const (by positivity)
  have h := (Real.zero_at_infty_fourier f).comp
    ((tendsto_id.mono_right atBot_le_cocompact).comp hs)
  have hc := h.const_mul ((1 / (2 * Real.pi) : ℝ) : ℂ)
  simpa only [Function.comp_def, id_eq, mul_zero, ← probabilityInverseIntegral_eq_fourier] using hc

lemma probabilityInverseIntegral_hasDerivAt {f : ℝ → ℂ} (hf : Integrable f)
    (htf : Integrable (fun t : ℝ => (-Complex.I * (t : ℂ)) * f t)) (x : ℝ) :
    HasDerivAt (probabilityInverseIntegral f)
      (probabilityInverseIntegral (fun t : ℝ => (-Complex.I * (t : ℂ)) * f t) x) x := by
  have hd (t y : ℝ) : HasDerivAt
      (fun z : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (z : ℂ)) * f t)
      (Complex.exp (-Complex.I * (t : ℂ) * (y : ℂ)) *
        ((-Complex.I * (t : ℂ)) * f t)) y := by
    convert (((Complex.ofRealCLM.hasDerivAt.const_mul (-Complex.I * (t : ℂ))).cexp).mul_const (f t)) using 1 <;> simp [Complex.ofRealCLM_apply, mul_comm, mul_left_comm, mul_assoc]
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (s := univ) (bound := fun t => ‖(-Complex.I * (t : ℂ)) * f t‖)
    (F := fun y t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (y : ℂ)) * f t)
    (F' := fun y t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (y : ℂ)) *
      ((-Complex.I * (t : ℂ)) * f t))
    (x₀ := x) (by simp)
    (Filter.Eventually.of_forall fun y => (probabilityInverseKernel_integrable hf y).1)
    (probabilityInverseKernel_integrable hf x)
    (probabilityInverseKernel_integrable htf x).1
    (ae_of_all _ fun t y _ => by rw [norm_mul, norm_probabilityInverseKernel, one_mul])
    htf.norm (ae_of_all _ fun t y _ => hd t y)
  exact hi.2.const_mul _

private noncomputable def realEuclideanEquiv : ℝ ≃ₗᵢ[ℝ] ProbabilityFoundations.Ch07.Euclidean 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

private lemma charFun_realEuclidean (μ : Measure ℝ) (t : ℝ) :
    charFun (μ.map realEuclideanEquiv) (realEuclideanEquiv t) = charFun μ t := by
  rw [charFun_apply, charFun_apply,
    integral_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  rw [realEuclideanEquiv.inner_map_map]

private lemma inverse_realEuclidean (μ : Measure ℝ) (x : ℝ) :
    ProbabilityFoundations.Ch07.inverseCharacteristicIntegral (μ.map realEuclideanEquiv)
      (realEuclideanEquiv x) = probabilityInverseIntegral (charFun μ) x := by
  rw [ProbabilityFoundations.Ch07.inverseCharacteristicIntegral, probabilityInverseIntegral]
  have hc : (2 * Real.pi) ^ (-(1 : ℝ)) = 1 / (2 * Real.pi) := by
    rw [Real.rpow_neg_one, one_div]
  simp only [Nat.cast_one, hc]
  congr 1
  rw [← realEuclideanEquiv.measurePreserving.integral_comp
    realEuclideanEquiv.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [realEuclideanEquiv.inner_map_map, charFun_realEuclidean]
  simp only [real_inner_comm]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- Real-line form of the accepted Euclidean density inversion theorem.
The density is used as a complex function, so differences and primitives need
no separate real/imaginary-part bookkeeping. -/
lemma real_inverse_density (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (charFun μ)) :
    Integrable (probabilityInverseIntegral (charFun μ)) ∧
    ∀ s : Set ℝ, MeasurableSet s →
      ((μ s).toReal : ℂ) = ∫ x in s, probabilityInverseIntegral (charFun μ) x := by
  let e := realEuclideanEquiv
  let m := μ.map e
  have : IsProbabilityMeasure m := inferInstance
  have hc : Integrable (charFun m) := by
    apply (e.measurePreserving.integrable_comp_emb e.toHomeomorph.measurableEmbedding).1
    simpa only [Function.comp_def, m, e, charFun_realEuclidean] using hμ
  obtain ⟨him, hn, hcont, hb, hi, h1, heq, hA⟩ :=
    ProbabilityFoundations.Ch07.integrable_characteristicFunction_density m hc
  let f := ProbabilityFoundations.Ch07.inverseCharacteristicDensity m
  have hfi : Integrable (fun x => f (e x)) :=
    e.measurePreserving.integrable_comp_of_integrable hi
  have hreal (x : ℝ) : probabilityInverseIntegral (charFun μ) x = (f (e x) : ℂ) := by
    rw [← inverse_realEuclidean]
    apply Complex.ext
    · rfl
    · exact him (e x)
  constructor
  · exact hfi.ofReal.congr (ae_of_all _ fun x => (hreal x).symm)
  · intro s hs
    have hs' : MeasurableSet (e.symm ⁻¹' s) := e.symm.continuous.measurable hs
    have hm : m (e.symm ⁻¹' s) = μ s := by
      rw [Measure.map_apply e.continuous.measurable hs']
      congr 1
      ext x
      simp
    have hset : (∫ y in e.symm ⁻¹' s, f y) = ∫ x in s, f (e x) := by
      have h := e.toHomeomorph.measurableEmbedding.setIntegral_map (μ := (volume : Measure ℝ)) f (e.symm ⁻¹' s)
      change (∫ y in e.symm ⁻¹' s, f y ∂(volume : Measure ℝ).map e) =
        ∫ x in e ⁻¹' (e.symm ⁻¹' s), f (e x) at h
      rw [e.measurePreserving.map_eq] at h
      have hpre : e ⁻¹' (e.symm ⁻¹' s) = s := by
        ext x
        simp
      simpa only [hpre] using h
    have hmass : μ s = ENNReal.ofReal (∫ x in s, f (e x)) := by
      rw [← hm, hA _ hs', hset]
    rw [hmass, ENNReal.toReal_ofReal (integral_nonneg fun x => hn (e x))]
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact ae_of_all _ fun x => (hreal x).symm

lemma probabilityInverseIntegral_sub {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (x : ℝ) :
    probabilityInverseIntegral (fun t => f t - g t) x =
      probabilityInverseIntegral f x - probabilityInverseIntegral g x := by
  simp only [probabilityInverseIntegral, mul_sub]
  rw [integral_sub (probabilityInverseKernel_integrable hf x)
    (probabilityInverseKernel_integrable hg x), mul_sub]

/-- An integrable inverse primitive of the characteristic-function difference
recovers the difference of CDFs, with the constant fixed by Riemann--Lebesgue. -/
lemma cdfDifference_eq_inverse (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (charFun μ)) (hν : Integrable (charFun ν))
    (f : ℝ → ℂ) (hf : Integrable f)
    (hrel : (fun t : ℝ => (-Complex.I * (t : ℂ)) * f t) =ᵐ[volume]
      (fun t => charFun μ t - charFun ν t)) (x : ℝ) :
    ((μ (Iic x)).toReal - (ν (Iic x)).toReal : ℂ) = probabilityInverseIntegral f x := by
  obtain ⟨hiμ, hAμ⟩ := real_inverse_density μ hμ
  obtain ⟨hiν, hAν⟩ := real_inverse_density ν hν
  have htf : Integrable (fun t : ℝ => (-Complex.I * (t : ℂ)) * f t) :=
    (hμ.sub hν).congr hrel.symm
  have hd (y : ℝ) : HasDerivAt (probabilityInverseIntegral f)
      (probabilityInverseIntegral (charFun μ) y - probabilityInverseIntegral (charFun ν) y) y := by
    have h := probabilityInverseIntegral_hasDerivAt hf htf y
    convert h using 1
    rw [← probabilityInverseIntegral_sub hμ hν]
    unfold probabilityInverseIntegral
    congr 1
    apply integral_congr_ae
    exact hrel.mono fun t ht => congrArg (fun z =>
      Complex.exp (-Complex.I * (t : ℂ) * (y : ℂ)) * z) ht.symm
  have hFTC := integral_Iic_of_hasDerivAt_of_tendsto' (a := x)
    (fun y _ => hd y) (hiμ.sub hiν).integrableOn
    (probabilityInverseIntegral_tendsto_atBot f)
  rw [sub_zero] at hFTC
  rw [hAμ _ measurableSet_Iic, hAν _ measurableSet_Iic,
    ← integral_sub hiμ.integrableOn hiν.integrableOn]
  exact hFTC

lemma charFun_smoothedLaw (μ : Measure ℝ) [IsFiniteMeasure μ]
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    (T t : ℝ) :
    charFun (smoothedLaw μ J T) t = charFun μ t * charFun (smoothingMeasure J) (t / T) := by
  have : IsProbabilityMeasure (smoothingMeasure J) := hJ.2.2.2.2.2.2.2.1
  rw [smoothedLaw, charFun_conv]
  congr 1
  have h := charFun_map_mul (μ := smoothingMeasure J) T⁻¹ t
  simpa only [div_eq_mul_inv, mul_comm] using h

lemma smoothedLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    (T : ℝ) : IsProbabilityMeasure (smoothedLaw μ J T) := by
  have : IsProbabilityMeasure (smoothingMeasure J) := hJ.2.2.2.2.2.2.2.1
  unfold smoothedLaw
  infer_instance

lemma smoothedLaw_charFun_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    {T : ℝ} (hT : 0 < T) : Integrable (charFun (smoothedLaw μ J T)) := by
  have := smoothedLaw_probability μ J hJ T
  apply continuous_charFun.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-T) T) isCompact_Icc
  intro t ht
  rw [charFun_smoothedLaw μ J hJ]
  have hc : charFun (smoothingMeasure J) (t / T) = 0 := by
    apply hJ.2.2.2.2.2.2.2.2.1
    rw [abs_div, abs_of_pos hT, lt_div_iff₀ hT, one_mul]
    exact lt_of_not_ge (fun hh => ht (abs_le.mp hh))
  rw [hc, mul_zero]

lemma smoothedCdfDifference_eq_inverse (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    {T : ℝ} (hT : 0 < T) (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hν : Integrable (fun x : ℝ => |x|) ν) (x : ℝ) :
    (smoothedCdf μ J T x - smoothedCdf ν J T x : ℂ) =
      inverseSmoothedQuotient μ ν J T x := by
  have := smoothedLaw_probability μ J hJ T
  have := smoothedLaw_probability ν J hJ T
  have hq := smoothedCharacteristicQuotient_integrable μ ν J hJ hT hμ hν
  apply cdfDifference_eq_inverse (smoothedLaw μ J T) (smoothedLaw ν J T)
    (smoothedLaw_charFun_integrable μ J hJ hT)
    (smoothedLaw_charFun_integrable ν J hJ hT)
    (fun t => Complex.I * smoothedCharacteristicQuotient μ ν J T t) (hq.const_mul _)
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  rw [smoothedCharacteristicQuotient_eq μ ν J T ht,
    smoothedCharacteristicDifference, charFun_smoothedLaw μ J hJ,
    charFun_smoothedLaw ν J hJ]
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  field_simp
  simp [Complex.I_sq]
  ring

lemma characteristicDifferenceQuotient_norm (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {t : ℝ} (ht : t ≠ 0) :
    ‖characteristicDifferenceQuotient μ ν t‖ = ‖charFun μ t - charFun ν t‖ / |t| := by
  rw [characteristicDifferenceQuotient_eq μ ν ht, norm_div, Complex.norm_real, Real.norm_eq_abs]

lemma characteristicDifferenceQuotient_norm_integrableOn (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => |x|) μ) (hν : Integrable (fun x : ℝ => |x|) ν)
    (T : ℝ) :
    IntegrableOn (fun t : ℝ => ‖charFun μ t - charFun ν t‖ / |t|) (Icc (-T) T) := by
  have hi := (characteristicDifferenceQuotient_continuous μ ν hμ hν).norm.continuousOn.integrableOn_Icc
    (μ := (volume : Measure ℝ)) (a := -T) (b := T)
  apply hi.congr
  filter_upwards [(volume.restrict (Icc (-T) T)).ae_ne (0 : ℝ)] with t ht
  exact characteristicDifferenceQuotient_norm μ ν ht

lemma smoothedCharacteristicQuotient_norm_le (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    (T : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ‖smoothedCharacteristicQuotient μ ν J T t‖ ≤ ‖charFun μ t - charFun ν t‖ / |t| := by
  rw [smoothedCharacteristicQuotient, norm_mul]
  apply (mul_le_mul_of_nonneg_left (hJ.2.2.2.2.2.2.2.2.2.1 (t / T)) (norm_nonneg _)).trans_eq
  rw [mul_one, characteristicDifferenceQuotient_norm μ ν ht]

lemma inverseSmoothedQuotient_norm_le (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    {T : ℝ} (hT : 0 < T) (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hν : Integrable (fun x : ℝ => |x|) ν) (x : ℝ) :
    ‖inverseSmoothedQuotient μ ν J T x‖ ≤ smoothingFourierBound μ ν T := by
  have hi := smoothedCharacteristicQuotient_integrable μ ν J hJ hT hμ hν
  have hb := characteristicDifferenceQuotient_norm_integrableOn μ ν hμ hν T
  have hsupport : (∫ t in Icc (-T) T, ‖smoothedCharacteristicQuotient μ ν J T t‖) =
      ∫ t : ℝ, ‖smoothedCharacteristicQuotient μ ν J T t‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hz : smoothedCharacteristicQuotient μ ν J T t = 0 :=
      Function.notMem_support.mp (fun h => ht (smoothedCharacteristicQuotient_support μ ν J hJ hT h))
    rw [hz, norm_zero]
  have hbound : (∫ t : ℝ, ‖smoothedCharacteristicQuotient μ ν J T t‖) ≤
      ∫ t in Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t| := by
    rw [← hsupport]
    apply integral_mono_ae hi.norm.integrableOn hb
    filter_upwards [(volume.restrict (Icc (-T) T)).ae_ne (0 : ℝ)] with t ht
    exact smoothedCharacteristicQuotient_norm_le μ ν J hJ T ht
  unfold inverseSmoothedQuotient smoothingFourierBound
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_integral_le_integral_norm _).trans
  simp only [norm_mul, norm_probabilityInverseKernel, Complex.norm_I, one_mul]
  exact hbound

/-- Complete integrable-quotient inversion, including the additive constant and
uniform estimate, with no equality-of-means assumption. -/
theorem smoothedCdfDifference_inversion :
    Specs.ProbabilityFoundations.Ch09.SmoothedCdfDifferenceInversion.SmoothedCdfInversion := by
  intro μ ν _ _ J hJ T hT hμ hν
  dsimp only
  have hq := smoothedCharacteristicQuotient_integrable μ ν J hJ hT hμ hν
  have hqi := hq.const_mul Complex.I
  have hzero : smoothedCharacteristicQuotient μ ν J T 0 =
      Complex.I * ((∫ x : ℝ, x ∂μ) - (∫ x : ℝ, x ∂ν) : ℝ) := by
    have : IsProbabilityMeasure (smoothingMeasure J) := hJ.2.2.2.2.2.2.2.1
    rw [smoothedCharacteristicQuotient, zero_div, charFun_zero]
    simpa using characteristicDifferenceQuotient_zero μ ν hμ hν
  have hcont : Continuous (inverseSmoothedQuotient μ ν J T) :=
    probabilityInverseIntegral_continuous hqi
  have hbot : Tendsto (inverseSmoothedQuotient μ ν J T) atBot (𝓝 0) :=
    probabilityInverseIntegral_tendsto_atBot _
  have hident := smoothedCdfDifference_eq_inverse μ ν J hJ hT hμ hν
  have hbound (x : ℝ) : |smoothedCdf μ J T x - smoothedCdf ν J T x| ≤
      smoothingFourierBound μ ν T := by
    have h := inverseSmoothedQuotient_norm_le μ ν J hJ hT hμ hν x
    rw [← hident x] at h
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  exact ⟨smoothedCharacteristicQuotient_continuous μ ν J hJ T hμ hν,
    (fun t ht => smoothedCharacteristicQuotient_eq μ ν J T ht), hzero,
    smoothedCharacteristicQuotient_support μ ν J hJ hT, hq,
    (fun x => probabilityInverseKernel_integrable hqi x), hcont, hbot, hident,
    characteristicDifferenceQuotient_norm_integrableOn μ ν hμ hν T,
    hbound, ciSup_le hbound⟩

end ProbabilityFoundations.Ch09
