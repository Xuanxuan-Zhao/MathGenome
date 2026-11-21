import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.BerryEsseenTheorem
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch09.BerryEsseenCharacteristicEstimate
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch09.EsseenSmoothingInequality
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ProbabilityFoundations.Ch09

/-- An integrable majorant for the smoothing integral. -/
lemma integrable_berry_gaussian_weight :
    Integrable (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 6)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 6 : ℝ))
    (by norm_num) (s := 2) (by norm_num)
  simpa only [Real.rpow_two, neg_mul, one_div_mul_eq_div, neg_div] using h

/-- The standard Gaussian has a finite first absolute moment. -/
lemma standard_normal_first_moment :
    Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
  simpa only [Real.norm_eq_abs, id_eq] using
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).norm

/-- Bounded density gives a global Lipschitz bound, with a numerical constant. -/
lemma standard_normal_cdf_lipschitz :
    ∀ x y : ℝ, |cdf (gaussianReal 0 1) x - cdf (gaussianReal 0 1) y| ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * |x - y| := by
  suffices h : ∀ a b : ℝ, a ≤ b →
      cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤
        (Real.sqrt (2 * Real.pi))⁻¹ * (b - a) by
    intro x y
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonpos (sub_nonpos.mpr (monotone_cdf _ hxy)),
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      simpa only [neg_sub] using h x y hxy
    · rw [abs_of_nonneg (sub_nonneg.mpr (monotone_cdf _ hyx)),
        abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact h y x hyx
  intro a b hab
  have hmass : cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a =
      ((gaussianReal 0 1) (Ioc a b)).toReal := by
    conv_rhs => rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc]
    exact (ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_cdf _ hab))).symm
  rw [hmass, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun t => gaussianPDFReal_nonneg 0 1 t))]
  have hbound : ∀ t : ℝ, gaussianPDFReal 0 1 t ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro t
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    apply mul_le_of_le_one_right (by positivity)
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have hi := integral_mono_ae (μ := volume.restrict (Ioc a b))
    (integrable_gaussianPDFReal 0 1).integrableOn
    (integrable_const (Real.sqrt (2 * Real.pi))⁻¹)
    (ae_of_all _ hbound)
  simpa [setIntegral_const, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    smul_eq_mul, mul_comm, max_eq_left (sub_nonneg.mpr hab)] using hi

/-- Characteristic function of the normalized iid sum, with the exact frequency
and power appearing in the upstream quantitative estimate. -/
lemma charFun_normalized_iid_sum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, Measurable (Y k)) (hi : iIndepFun Y P)
    (hd : ∀ k, P.map (Y k) = P.map (Y 0)) (n : ℕ) (t : ℝ) :
    charFun (P.map (fun ω => (∑ k ∈ Finset.range n, Y k ω) /
      Real.sqrt (n : ℝ))) t =
      charFun (P.map (Y 0)) (t / Real.sqrt (n : ℝ)) ^ n := by
  have hs : Measurable (fun ω => ∑ k ∈ Finset.range n, Y k ω) := by fun_prop
  have he : (fun ω => (∑ k ∈ Finset.range n, Y k ω) / Real.sqrt (n : ℝ)) =
      (fun ω => (Real.sqrt (n : ℝ))⁻¹ * (∑ k ∈ Finset.range n, Y k ω)) := by
    ext ω
    ring
  rw [he, charFun_map_mul_comp hs.aemeasurable]
  have h := congrFun ((hi.restrict (Finset.range n)).charFun_map_fun_finsetSum_eq_prod
    (fun k _ => (hY k).aemeasurable)) ((Real.sqrt (n : ℝ))⁻¹ * t)
  simp only [Finset.prod_apply] at h
  rw [h]
  simp_rw [hd]
  simp [div_eq_mul_inv, mul_comm]

/-- The integral transform term is bounded uniformly in the cutoff by the
finite Gaussian moment. The value assigned to the quotient at zero is harmless. -/
lemma berry_smoothing_integral_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (K T : ℝ) (hK : 0 ≤ K)
    (hi : IntegrableOn (fun t : ℝ =>
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) (Icc (-T) T))
    (he : ∀ t ∈ Icc (-T) T,
      ‖charFun μ t - (Real.exp (-t ^ 2 / 2) : ℂ)‖ ≤
        K * |t| ^ 3 * Real.exp (-t ^ 2 / 6)) :
    (∫ t in Icc (-T) T, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) ≤
      K * ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 6) := by
  have hg (t : ℝ) : charFun (gaussianReal 0 1) t =
      (Real.exp (-t ^ 2 / 2) : ℂ) := by
    rw [charFun_gaussianReal]
    simp only [NNReal.coe_one, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hpoint : ∀ t ∈ Icc (-T) T,
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t| ≤
        K * (t ^ 2 * Real.exp (-t ^ 2 / 6)) := by
    intro t ht
    rw [hg]
    by_cases ht0 : t = 0
    · simp [ht0]
    · calc
        _ ≤ (K * |t| ^ 3 * Real.exp (-t ^ 2 / 6)) / |t| :=
          div_le_div_of_nonneg_right (he t ht) (abs_nonneg t)
        _ = _ := by
          rw [show |t| ^ 3 = t ^ 2 * |t| by rw [pow_succ, sq_abs]]
          field_simp [abs_ne_zero.mpr ht0]
  calc
    _ ≤ ∫ t in Icc (-T) T, K * (t ^ 2 * Real.exp (-t ^ 2 / 6)) :=
      integral_mono_ae hi (integrable_berry_gaussian_weight.const_mul K).integrableOn
        ((ae_restrict_mem measurableSet_Icc).mono hpoint)
    _ = K * ∫ t in Icc (-T) T, t ^ 2 * Real.exp (-t ^ 2 / 6) := integral_const_mul _ _
    _ ≤ K * ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 6) := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact setIntegral_le_integral integrable_berry_gaussian_weight
        (ae_of_all _ fun t => by positivity)

/-- Berry–Esseen for centered unit-variance summands. Constants are chosen
before the probability space, the summands, and the sample size. -/
theorem berry_esseen_standardized :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ),
      (∀ k, Measurable (Y k)) → iIndepFun Y P →
      (∀ k, P.map (Y k) = P.map (Y 0)) →
      Integrable (fun ω => |Y 0 ω| ^ 3) P →
      (∫ ω, Y 0 ω ∂P) = 0 → (∫ ω, Y 0 ω ^ 2 ∂P) = 1 →
      ∀ n : ℕ, 1 ≤ n →
      (⨆ x : ℝ, |cdf (P.map (fun ω => (∑ k ∈ Finset.range n, Y k ω) /
        Real.sqrt (n : ℝ))) x - cdf (gaussianReal 0 1) x|) ≤
        (C / Real.sqrt (n : ℝ)) * ∫ ω, |Y 0 ω| ^ 3 ∂P := by
  obtain ⟨c, C₀, hc, hc1, hC₀, hestimate⟩ := berry_esseen_characteristic_estimate
  obtain ⟨Cs, hCs, hsmoothing⟩ := esseen_smoothing_inequality
  let A : ℝ := ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 6)
  let M : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hA : 0 ≤ A := integral_nonneg (fun t => by positivity)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let C : ℝ := 1 + Cs * (C₀ * A + M / c)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by
    have : 0 ≤ Cs * (C₀ * A + M / c) := by positivity
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro Ω mΩ P instP Y hY hi hd h3 h0 h2 n hn
  let ρ : ℝ := ∫ ω, |Y 0 ω| ^ 3 ∂P
  obtain ⟨hρ, hest⟩ := hestimate P (Y 0) (hY 0) h3 h0 h2
  change 1 ≤ ρ at hρ
  have hρpos : 0 < ρ := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  let S : Ω → ℝ := fun ω => (∑ k ∈ Finset.range n, Y k ω) / Real.sqrt (n : ℝ)
  have hS : Measurable S := by dsimp [S]; fun_prop
  let μ := P.map S
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  change (⨆ x : ℝ, |cdf μ x - cdf (gaussianReal 0 1) x|) ≤ (C / _) * ρ
  by_cases hn1 : n = 1
  · subst n
    simp only [Nat.cast_one, Real.sqrt_one, div_one]
    have hbound : (⨆ x : ℝ, |cdf μ x - cdf (gaussianReal 0 1) x|) ≤ 1 := by
      apply ciSup_le
      intro x
      exact abs_le.mpr ⟨by linarith [cdf_nonneg μ x, cdf_le_one (gaussianReal 0 1) x],
        by linarith [cdf_le_one μ x, cdf_nonneg (gaussianReal 0 1) x]⟩
    exact hbound.trans (by nlinarith)
  have hn2 : 2 ≤ n := by omega
  have hLp : MemLp (Y 0) 3 P := by
    apply (integrable_norm_rpow_iff (hY 0).aestronglyMeasurable
      (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num : (3 : ℝ≥0∞) ≠ ∞)).mp
    simpa using h3
  have hint0 : Integrable (Y 0) P := hLp.integrable (by norm_num)
  have hint (k : ℕ) : Integrable (Y k) P := by
    have hm : Integrable (fun x : ℝ => x) (P.map (Y 0)) :=
      (integrable_map_measure measurable_id.aestronglyMeasurable (hY 0).aemeasurable).mpr hint0
    rw [← hd k] at hm
    exact (integrable_map_measure measurable_id.aestronglyMeasurable (hY k).aemeasurable).mp hm
  have hiS : Integrable S P := (integrable_finsetSum _ (fun k _ => hint k)).div_const _
  have hμ : Integrable (fun x : ℝ => |x|) μ := by
    apply (integrable_map_measure (by fun_prop) hS.aemeasurable).mpr
    simpa only [Real.norm_eq_abs, Function.comp_def] using hiS.norm
  let T : ℝ := c * Real.sqrt (n : ℝ) / ρ
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨hiQ, hsm⟩ := hsmoothing μ (gaussianReal 0 1) hμ standard_normal_first_moment
    M hM (fun x y => by simpa only [distributionFunction_eq_cdf] using
      standard_normal_cdf_lipschitz x y) T hT
  simp only [distributionFunction_eq_cdf] at hsm
  have he : ∀ t ∈ Icc (-T) T,
      ‖charFun μ t - (Real.exp (-t ^ 2 / 2) : ℂ)‖ ≤
        (C₀ * ρ / Real.sqrt (n : ℝ)) * |t| ^ 3 * Real.exp (-t ^ 2 / 6) := by
    intro t ht
    change ‖charFun (P.map S) t - _‖ ≤ _
    rw [show S = (fun ω => (∑ k ∈ Finset.range n, Y k ω) / Real.sqrt (n : ℝ)) from rfl,
      charFun_normalized_iid_sum P Y hY hi hd n t]
    exact hest n hn2 t (abs_le.mpr ht)
  have hI := berry_smoothing_integral_bound μ (C₀ * ρ / Real.sqrt (n : ℝ)) T
    (by positivity) hiQ he
  change (∫ t in Icc (-T) T, _) ≤ (C₀ * ρ / Real.sqrt (n : ℝ)) * A at hI
  have hMT : M / T = (M / c) * ρ / Real.sqrt (n : ℝ) := by
    dsimp [T]
    field_simp
  calc
    _ ≤ Cs * ((∫ t in Icc (-T) T, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) + M / T) := hsm
    _ ≤ Cs * ((C₀ * ρ / Real.sqrt (n : ℝ)) * A + M / T) := by gcongr
    _ = (Cs * (C₀ * A + M / c) / Real.sqrt (n : ℝ)) * ρ := by rw [hMT]; ring
    _ ≤ (C / Real.sqrt (n : ℝ)) * ρ := by
      apply mul_le_mul_of_nonneg_right _ hρpos.le
      apply div_le_div_of_nonneg_right _ hs.le
      dsimp [C]
      linarith

/-- Berry–Esseen with the actual mean and positive standard deviation,
including all real thresholds and every positive sample size. -/
theorem berry_esseen :
    Specs.ProbabilityFoundations.Ch09.BerryEsseenTheorem.BerryEsseen := by
  obtain ⟨C, hC, hbound⟩ := berry_esseen_standardized
  refine ⟨C, hC, ?_⟩
  intro Ω mΩ P instP X hX hi hd m σ hσ hm hv h3 n hn
  let Y : ℕ → Ω → ℝ := fun k ω => (X k ω - m) / σ
  have hY : ∀ k, Measurable (Y k) := by intro k; dsimp [Y]; fun_prop
  have hiY : iIndepFun Y P := hi.comp (fun _ x => (x - m) / σ) (by fun_prop)
  have hdY : ∀ k, P.map (Y k) = P.map (Y 0) := by
    intro k
    calc
      _ = (P.map (X k)).map (fun x => (x - m) / σ) :=
        (Measure.map_map (by fun_prop) (hX k)).symm
      _ = (P.map (X 0)).map (fun x => (x - m) / σ) := by rw [hd k]
      _ = _ := Measure.map_map (by fun_prop) (hX 0)
  have hi3Y : Integrable (fun ω => |Y 0 ω| ^ 3) P := by
    simpa only [Y, abs_div, abs_of_pos hσ, div_pow] using h3.div_const (σ ^ 3)
  have hcenterLp : MemLp (fun ω => X 0 ω - m) 3 P := by
    apply (integrable_norm_rpow_iff (by fun_prop)
      (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num : (3 : ℝ≥0∞) ≠ ∞)).mp
    simpa using h3
  have hicenter : Integrable (fun ω => X 0 ω - m) P := hcenterLp.integrable (by norm_num)
  have hiX : Integrable (X 0) P := by
    have he : (fun ω => X 0 ω - m) + (fun _ : Ω => m) = X 0 := by
      ext ω
      simp
    rw [← he]
    exact hicenter.add (integrable_const m)
  have hY0 : (∫ ω, Y 0 ω ∂P) = 0 := by
    dsimp [Y]
    rw [integral_div, integral_sub hiX (integrable_const m), hm]
    simp
  have hY2 : (∫ ω, Y 0 ω ^ 2 ∂P) = 1 := by
    dsimp [Y]
    simp_rw [div_pow]
    rw [integral_div, hv, div_self (pow_ne_zero _ hσ.ne')]
  have hY3 : (∫ ω, |Y 0 ω| ^ 3 ∂P) = (∫ ω, |X 0 ω - m| ^ 3 ∂P) / σ ^ 3 := by
    dsimp [Y]
    simp_rw [abs_div, abs_of_pos hσ, div_pow]
    exact integral_div _ _
  have h := hbound P Y hY hiY hdY hi3Y hY0 hY2 n hn
  let S : Ω → ℝ := fun ω => (∑ k ∈ Finset.range n, Y k ω) / Real.sqrt (n : ℝ)
  have hS : Measurable S := by dsimp [S]; fun_prop
  have : IsProbabilityMeasure (P.map S) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  have heS (ω : Ω) : S ω =
      (∑ k ∈ Finset.range n, (X k ω - m)) / (σ * Real.sqrt (n : ℝ)) := by
    dsimp [S, Y]
    rw [← Finset.sum_div]
    ring
  have hcdf (x : ℝ) : cdf (P.map S) x =
      (P {ω | (∑ k ∈ Finset.range n, (X k ω - m)) /
        (σ * Real.sqrt (n : ℝ)) ≤ x}).toReal := by
    rw [cdf_eq_real]
    change (P.map S (Iic x)).toReal = _
    rw [Measure.map_apply hS measurableSet_Iic]
    congr 2
    ext ω
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq, heS]
  change (⨆ x : ℝ, |cdf (P.map S) x - cdf (gaussianReal 0 1) x|) ≤
    (C / Real.sqrt (n : ℝ)) * (∫ ω, |Y 0 ω| ^ 3 ∂P) at h
  simp_rw [hcdf, cdf_eq_real, hY3] at h
  convert h using 1 <;> simp only [Measure.real, mul_div_assoc]

end ProbabilityFoundations.Ch09
