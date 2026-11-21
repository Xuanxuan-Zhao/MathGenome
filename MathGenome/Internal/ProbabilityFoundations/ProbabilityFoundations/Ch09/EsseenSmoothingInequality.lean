import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.EsseenSmoothingInequality
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch09.SmoothingKernel
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch09.SmoothedCdfDifferenceInversion
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

namespace ProbabilityFoundations.Ch09

lemma distributionFunction_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    Specs.ProbabilityFoundations.Ch01.RealDistributionFunctions.distributionFunctionValue μ x =
      cdf μ x := (cdf_eq_real μ x).symm

lemma cdf_shift_integrable (μ K : Measure ℝ) [IsProbabilityMeasure μ] [IsFiniteMeasure K]
    (a T : ℝ) : Integrable (fun w : ℝ => cdf μ (a - w / T)) K := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((monotone_cdf μ).measurable.comp (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg μ _)]
      exact cdf_le_one μ _

/-- A CDF of a convolution is the expectation of the shifted CDF. Atoms in
both measures are allowed. -/
lemma cdf_conv (μ K : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure K]
    (x : ℝ) : cdf (μ.conv K) x = ∫ w : ℝ, cdf μ (x - w) ∂K := by
  let f : ℝ → ℝ := (Iic x).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator measurableSet_Iic
  have hi : Integrable (fun p : ℝ × ℝ => f (p.1 + p.2)) (μ.prod K) := by
    apply (integrable_const (1 : ℝ)).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
    exact ae_of_all _ fun p => by simp [f, Set.indicator_apply]; split_ifs <;> norm_num
  rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
  change (∫ z, f z ∂(μ.prod K).map (fun p : ℝ × ℝ => p.1 + p.2)) = _
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable, integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [] with w
  have he : (fun y => f (y + w)) = (Iic (x - w)).indicator (fun _ => (1 : ℝ)) := by
    ext y
    simp only [f, Set.indicator_apply, mem_Iic]
    congr 1
    exact propext (by constructor <;> intro h <;> linarith)
  rw [he, integral_indicator measurableSet_Iic, setIntegral_const]
  simpa only [smul_eq_mul, mul_one] using (cdf_eq_real μ (x - w)).symm

lemma smoothedCdf_eq_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (J : ℝ → ℝ) (hJ : Specs.ProbabilityFoundations.Ch09.SmoothingKernel.KernelProperties J)
    (T x : ℝ) : smoothedCdf μ J T x =
      ∫ w : ℝ, cdf μ (x - w / T) ∂smoothingMeasure J := by
  have : IsProbabilityMeasure (smoothingMeasure J) := hJ.2.2.2.2.2.2.2.1
  have := smoothedLaw_probability μ J hJ T
  rw [smoothedCdf, distributionFunction_eq_cdf, smoothedLaw, cdf_conv]
  exact integral_map (by fun_prop)
    ((monotone_cdf μ).measurable.comp (by fun_prop)).aestronglyMeasurable

/-- A fixed finite radius captures more than three quarters of any real
probability law. -/
lemma exists_central_radius (K : Measure ℝ) [IsProbabilityMeasure K] :
    ∃ b : ℝ, 0 < b ∧ (3 / 4 : ℝ) < K.real (Icc (-b) b) := by
  have hm : Monotone (fun n : ℕ => Icc (-(n : ℝ)) (n : ℝ)) := by
    intro n m hnm x hx
    have h : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hu : (⋃ n : ℕ, Icc (-(n : ℝ)) (n : ℝ)) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact mem_iUnion.2 ⟨n, abs_le.1 hn.le⟩
  have ht := tendsto_measure_iUnion_atTop (μ := K) hm
  rw [hu, measure_univ] at ht
  have hr := (ENNReal.tendsto_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).comp ht
  simp only [ENNReal.toReal_one] at hr
  obtain ⟨n, hn⟩ := (hr.eventually (lt_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1))).exists
  refine ⟨(n : ℝ) + 1, by positivity, hn.trans_le ?_⟩
  refine measureReal_mono ?_ (by finiteness)
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Integrate a lower bound on a central event and a uniform lower bound on
its complement. -/
lemma central_integral_lower (K : Measure ℝ) [IsProbabilityMeasure K]
    (b L d : ℝ) (f : ℝ → ℝ) (hf : Integrable f K)
    (hg : ∀ w ∈ Icc (-b) b, L ≤ f w) (hb : ∀ w, -d ≤ f w) :
    K.real (Icc (-b) b) * L - (1 - K.real (Icc (-b) b)) * d ≤ ∫ w, f w ∂K := by
  have h₁ : K.real (Icc (-b) b) * L ≤ ∫ w in Icc (-b) b, f w ∂K := by
    simpa only [setIntegral_const, smul_eq_mul] using
      integral_mono_ae (integrable_const L) hf.integrableOn
        ((ae_restrict_mem measurableSet_Icc).mono fun w hw => hg w hw)
  have h₂ : K.real (Icc (-b) b)ᶜ * (-d) ≤ ∫ w in (Icc (-b) b)ᶜ, f w ∂K := by
    simpa only [setIntegral_const, smul_eq_mul] using
      integral_mono_ae (integrable_const (-d)) hf.integrableOn (ae_of_all _ hb)
  rw [measureReal_compl measurableSet_Icc, probReal_univ] at h₂
  have he := integral_add_compl (μ := K) (s := Icc (-b) b) measurableSet_Icc hf
  linarith

/-- Monotonicity of the first CDF and Lipschitz regularity of the second CDF
remove the smoothing. This estimate uses no regularity of the first law. -/
lemma cdf_desmoothing (μ ν K : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure K]
    (b : ℝ) (hb : 0 < b) (hq : (3 / 4 : ℝ) < K.real (Icc (-b) b))
    (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x y : ℝ, |cdf ν x - cdf ν y| ≤ M * |x - y|)
    (T : ℝ) (hT : 0 < T) (A : ℝ)
    (hA : ∀ x : ℝ, |∫ w : ℝ, (cdf μ (x - w / T) - cdf ν (x - w / T)) ∂K| ≤ A) :
    (⨆ x : ℝ, |cdf μ x - cdf ν x|) ≤ 2 * A + 4 * b * (M / T) := by
  let d := ⨆ x : ℝ, |cdf μ x - cdf ν x|
  let q := K.real (Icc (-b) b)
  let E := 2 * M * b / T
  have hbd : BddAbove (range (fun x : ℝ => |cdf μ x - cdf ν x|)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact abs_le.2 ⟨by linarith [cdf_nonneg μ x, cdf_le_one ν x],
      by linarith [cdf_le_one μ x, cdf_nonneg ν x]⟩
  have hd (x : ℝ) : |cdf μ x - cdf ν x| ≤ d := le_ciSup hbd x
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0)
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := measureReal_le_one
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hi (x : ℝ) : Integrable (fun w : ℝ => cdf μ (x - w / T) - cdf ν (x - w / T)) K :=
    (cdf_shift_integrable μ K x T).sub (cdf_shift_integrable ν K x T)
  have hpoint (x : ℝ) : q * |cdf μ x - cdf ν x| ≤ A + (1 - q) * d + q * E := by
    have hp : q * (cdf μ x - cdf ν x - E) - (1 - q) * d ≤ A := by
      apply (central_integral_lower K b (cdf μ x - cdf ν x - E) d
        (fun w => cdf μ (x + b / T - w / T) - cdf ν (x + b / T - w / T))
        (hi (x + b / T)) ?_ ?_).trans
      · exact (le_abs_self _).trans (hA _)
      · intro w hw
        have hy₁ : x ≤ x + b / T - w / T := by
          have hh := (div_le_div_of_nonneg_right hw.2 hT.le)
          linarith only [hh]
        have hy₂ : x + b / T - w / T - x ≤ 2 * b / T := by
          have hh := (div_le_div_of_nonneg_right hw.1 hT.le)
          simp only [neg_div, mul_div_assoc] at *
          linarith only [hh]
        have hf := monotone_cdf μ hy₁
        have hg := (le_abs_self _).trans (hG (x + b / T - w / T) x)
        rw [abs_of_nonneg (sub_nonneg.2 hy₁)] at hg
        have hh := mul_le_mul_of_nonneg_left hy₂ hM
        have he : M * (2 * b / T) = E := by dsimp [E]; ring
        rw [he] at hh
        linarith [hg.trans hh]
      · intro w
        exact (neg_le_of_abs_le (hd _))
    have hn : q * (cdf ν x - cdf μ x - E) - (1 - q) * d ≤ A := by
      have hint := central_integral_lower K b (cdf ν x - cdf μ x - E) d
        (fun w => cdf ν (x - b / T - w / T) - cdf μ (x - b / T - w / T))
        ((cdf_shift_integrable ν K (x - b / T) T).sub (cdf_shift_integrable μ K (x - b / T) T))
      have hgood : ∀ w ∈ Icc (-b) b,
          cdf ν x - cdf μ x - E ≤ cdf ν (x - b / T - w / T) - cdf μ (x - b / T - w / T) := by
        intro w hw
        have hy₁ : x - b / T - w / T ≤ x := by
          have hh := (div_le_div_of_nonneg_right hw.1 hT.le)
          simp only [neg_div] at hh
          linarith only [hh]
        have hy₂ : x - (x - b / T - w / T) ≤ 2 * b / T := by
          have hh := (div_le_div_of_nonneg_right hw.2 hT.le)
          simp only [mul_div_assoc] at *
          linarith only [hh]
        have hf := monotone_cdf μ hy₁
        have hg := (le_abs_self _).trans (hG x (x - b / T - w / T))
        rw [abs_of_nonneg (sub_nonneg.2 hy₁)] at hg
        have hh := mul_le_mul_of_nonneg_left hy₂ hM
        have he : M * (2 * b / T) = E := by dsimp [E]; ring
        rw [he] at hh
        linarith [hg.trans hh]
      have hbad (w : ℝ) : -d ≤ cdf ν (x - b / T - w / T) - cdf μ (x - b / T - w / T) := by
        have := (le_abs_self _).trans (hd (x - b / T - w / T))
        linarith
      have h := hint hgood hbad
      have he : (∫ w : ℝ, (cdf ν (x - b / T - w / T) - cdf μ (x - b / T - w / T)) ∂K) =
          -(∫ w : ℝ, (cdf μ (x - b / T - w / T) - cdf ν (x - b / T - w / T)) ∂K) := by
        rw [← integral_neg]
        congr 1
        ext w
        ring
      rw [he] at h
      exact h.trans ((neg_le_abs _).trans (hA _))
    rcases le_total 0 (cdf μ x - cdf ν x) with hx | hx
    · rw [abs_of_nonneg hx]
      dsimp [q] at *
      nlinarith [hp]
    · rw [abs_of_nonpos hx]
      dsimp [q] at *
      nlinarith [hn]
  have hd' : d ≤ (A + (1 - q) * d + q * E) / q := by
    apply ciSup_le
    intro x
    exact (le_div_iff₀ hq0).2 (by simpa [mul_comm] using hpoint x)
  have hmul := (le_div_iff₀ hq0).1 hd'
  have hq' : (3 / 4 : ℝ) < q := hq
  have he' : q * E ≤ E := by nlinarith
  have hdq : (1 / 2 : ℝ) * d ≤ (2 * q - 1) * d := by nlinarith
  have hfinal : d ≤ 2 * A + 2 * E := by nlinarith
  dsimp [E] at hfinal
  change d ≤ _
  convert hfinal using 1; ring

/-- Esseen's inequality for arbitrary real probability laws with finite first
absolute moments. The comparison CDF alone is required to be Lipschitz. -/
theorem esseen_smoothing_inequality :
    Specs.ProbabilityFoundations.Ch09.EsseenSmoothingInequality.SmoothingInequality := by
  obtain ⟨J, hJ⟩ := exists_smoothingKernel
  have : IsProbabilityMeasure (smoothingMeasure J) := hJ.2.2.2.2.2.2.2.1
  obtain ⟨b, hb, hq⟩ := exists_central_radius (smoothingMeasure J)
  let c : ℝ := 2 * (1 / (2 * Real.pi) + 2 * b + 1)
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro μ ν _ _ hμ hν M hM hG T hT
  refine ⟨characteristicDifferenceQuotient_norm_integrableOn μ ν hμ hν T, ?_⟩
  have hG' (x y : ℝ) : |cdf ν x - cdf ν y| ≤ M * |x - y| := by
    simpa only [distributionFunction_eq_cdf] using hG x y
  have hA (x : ℝ) :
      |∫ w : ℝ, (cdf μ (x - w / T) - cdf ν (x - w / T)) ∂smoothingMeasure J| ≤
        smoothingFourierBound μ ν T := by
    rw [integral_sub (cdf_shift_integrable μ (smoothingMeasure J) x T)
      (cdf_shift_integrable ν (smoothingMeasure J) x T),
      ← smoothedCdf_eq_integral μ J hJ T x, ← smoothedCdf_eq_integral ν J hJ T x]
    have h := inverseSmoothedQuotient_norm_le μ ν J hJ hT hμ hν x
    rw [← smoothedCdfDifference_eq_inverse μ ν J hJ hT hμ hν x] at h
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  have hd := cdf_desmoothing μ ν (smoothingMeasure J) b hb hq M hM hG' T hT
    (smoothingFourierBound μ ν T) hA
  simp only [distributionFunction_eq_cdf]
  apply hd.trans
  have hI : 0 ≤ ∫ t in Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t| := by
    apply integral_nonneg
    intro t
    positivity
  have hMT : 0 ≤ M / T := div_nonneg hM hT.le
  dsimp [smoothingFourierBound, c]
  have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
  nlinarith

end ProbabilityFoundations.Ch09
