import MathGenome.Internal.RealAnalysis.D11.Ch13.MaximalWeak11
import MathGenome.Internal.RealAnalysis.D11.Ch11.CcDensityEuclidean
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.LebesgueDifferentiation
import Mathlib.MeasureTheory.Integral.Average

/-! Direct maximal-estimate proof of function differentiation. No
Radon–Nikodym or AC/BV fundamental theorem is used. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
universe u
namespace D11.Ch13.LebesgueDifferentiation
open D11.Ch03 D11.Ch03.LebesgueMeasures
open D11.Ch13.AveragesMaximalDefinition
open D11.Ch13.MaximalWeak11
local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace n
variable {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

lemma average_eq_setAverage (f : Point n → 𝕜) (hf : locallyIntegrable f) (r : ℝ) (x : Point n) :
    average f hf r x = ⨍ y in ball x r, f y ∂(lebesgue n) := by
  rw [setAverage_eq]
  rfl

lemma oscillation_eq_setAverage (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (r : ℝ) (x : Point n) :
    oscillationAverage f hf r x = ⨍ y in ball x r, ‖f y - f x‖ ∂(lebesgue n) := by
  rw [setAverage_eq]
  rfl

lemma integrableOn_ball (f : Point n → 𝕜) (hf : locallyIntegrable f) (x : Point n) (r : ℝ) :
    IntegrableOn f (ball x r) (lebesgue n) :=
  ((D11.Ch06.ScalarIntegral.scalarIntegrable_iff _ _).mp (scalarIntegrable_ball f hf x r)).2

lemma oscillation_nonneg (f : Point n → 𝕜) (hf : locallyIntegrable f) (r : ℝ) (x : Point n) :
    0 ≤ oscillationAverage f hf r x := by
  rw [oscillation_eq_setAverage]
  exact average_nonneg (fun _ => norm_nonneg _)

lemma continuous_lebesguePoint (g : Point n → 𝕜) (hg : locallyIntegrable g)
    {x : Point n} (hc : ContinuousAt g x) : lebesguePoint g hg x := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun r => ha.trans_le (oscillation_nonneg g hg r x))
  · intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (half_pos hε)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with r hr hrd
    have hm := ball_measure x r hr
    have hi := (integrableOn_ball g hg x r).sub (integrableOn_const (C := g x) hm.2.1.ne)
    have hle : oscillationAverage g hg r x ≤ ε / 2 := by
      rw [oscillation_eq_setAverage, setAverage_eq]
      have hb : (∫ y in ball x r, ‖g y - g x‖ ∂(lebesgue n)) ≤
          ∫ _y in ball x r, ε / 2 ∂(lebesgue n) := by
        apply integral_mono_ae hi.norm (integrableOn_const hm.2.1.ne)
        filter_upwards [ae_restrict_mem (ball_measurable x r)] with y hy
        exact (show ‖g y - g x‖ < ε / 2 from by
          simpa only [dist_eq_norm] using hball (lt_trans hy hrd)).le
      have hs := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (ENNReal.toReal_nonneg (a := lebesgue n (ball x r))))
      simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ hm.2.2.ne', one_mul] using hs
    exact hle.trans_lt (half_lt_self hε)

lemma oscillation_comparison (f g : Point n → 𝕜) (hf : locallyIntegrable f)
    (hg : locallyIntegrable g) (he : locallyIntegrable (fun y => f y - g y))
    (x : Point n) (r : ℝ) (hr : 0 < r) :
    oscillationAverage f hf r x ≤ absoluteAverage (fun y => f y - g y) he r x +
      ‖f x - g x‖ + oscillationAverage g hg r x := by
  have hm := ball_measure x r hr
  have hfi := integrableOn_ball f hf x r
  have hgi := integrableOn_ball g hg x r
  have hconst (c : 𝕜) := integrableOn_const (μ := lebesgue n) (s := ball x r) (C := c) hm.2.1.ne
  have hcn : IntegrableOn (fun _ : Point n => ‖f x - g x‖) (ball x r) (lebesgue n) :=
    integrableOn_const hm.2.1.ne
  have hei : IntegrableOn (fun y => ‖f y - g y‖) (ball x r) (lebesgue n) :=
    (hfi.sub hgi).norm
  have hgo : IntegrableOn (fun y => ‖g y - g x‖) (ball x r) (lebesgue n) :=
    (hgi.sub (hconst (g x))).norm
  have hb : (∫ y in ball x r, ‖f y - f x‖ ∂(lebesgue n)) ≤
      ∫ y in ball x r, (‖f y - g y‖ + ‖f x - g x‖ + ‖g y - g x‖) ∂(lebesgue n) := by
    apply integral_mono_ae (hfi.sub (hconst (f x))).norm ((hei.add hcn).add hgo)
    exact ae_of_all _ (fun y => by
      calc
        ‖f y - f x‖ = ‖(f y - g y) - (f x - g x) + (g y - g x)‖ := by congr 1; abel
        _ ≤ ‖(f y - g y) - (f x - g x)‖ + ‖g y - g x‖ := norm_add_le _ _
        _ ≤ ‖f y - g y‖ + ‖f x - g x‖ + ‖g y - g x‖ := by gcongr; exact norm_sub_le _ _)
  have ha := integral_add (hei.add hcn) hgo
  have ha' := integral_add hei hcn
  simp only [Pi.add_apply] at ha ha'
  rw [ha, ha', integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul] at hb
  have hs := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (ENNReal.toReal_nonneg (a := lebesgue n (ball x r))))
  change _ ≤ _ at hs
  change (lebesgue n (ball x r)).toReal⁻¹ * _ ≤
    (lebesgue n (ball x r)).toReal⁻¹ * _ + ‖f x - g x‖ +
    (lebesgue n (ball x r)).toReal⁻¹ * _
  simpa only [D11.Ch06.ScalarIntegral.scalarIntegral, mul_add, ← mul_assoc,
    inv_mul_cancel₀ hm.2.2.ne', one_mul] using hs

/-- The accepted Cc density theorem, on representatives and with an L1 error. -/
lemma exists_cc_integral_lt (f : Point n → 𝕜) (hi : Integrable f (lebesgue n))
    {η : ℝ} (hη : 0 < η) :
    ∃ g : CompactlySupportedContinuousMap (Point n) 𝕜,
      Integrable (g : Point n → 𝕜) (lebesgue n) ∧
      (∫ y, ‖f y - g y‖ ∂(lebesgue n)) < η := by
  let hf := memLp_one_iff_integrable.mpr hi
  obtain ⟨g, hg, herr⟩ := D11.Ch11.CcDensityEuclidean.cc_density n 𝕜 1 (by simp)
    (hf.toLp f) η hη
  have hgi := memLp_one_iff_integrable.mp hg
  refine ⟨g, hgi, ?_⟩
  change MemLp (g : Point n → 𝕜) 1 (lebesgue n) at hg
  have heq := L1.norm_of_fun_eq_integral_norm (hi.sub hgi)
  simp only [Pi.sub_apply] at heq
  rw [← heq]
  change ‖(hf.sub hg).toLp (f - (g : Point n → 𝕜))‖ < η
  rw [MemLp.toLp_sub]
  exact herr

/-- Pointwise error is controlled in outer measure by Markov. -/
lemma error_level_bound (e : Point n → 𝕜) (hm : Measurable e)
    (hi : Integrable e (lebesgue n)) (ε : ℝ) (hε : 0 < ε) :
    lebesgue n {x | ε < ‖e x‖} ≤ (ENNReal.ofReal ε)⁻¹ *
      ENNReal.ofReal (∫ y, ‖e y‖ ∂(lebesgue n)) := by
  have hb := meas_ge_le_lintegral_div (μ := lebesgue n)
    (ENNReal.measurable_ofReal.comp hm.norm).aemeasurable
    (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top
  simp only [Function.comp_apply] at hb
  calc
    _ ≤ lebesgue n {x | ENNReal.ofReal ε ≤ ENNReal.ofReal ‖e x‖} :=
      measure_mono (fun x hx => ENNReal.ofReal_le_ofReal hx.le)
    _ ≤ _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi.norm
        (ae_of_all _ (fun y => norm_nonneg (e y)))] at hb
      simpa only [div_eq_mul_inv, mul_comm] using hb

/-- Failure of an eventual small-oscillation bound; no measurability of
this set is needed because all measure estimates are outer estimates. -/
def badOscillation (f : Point n → 𝕜) (hf : locallyIntegrable f) (ε : ℝ) : Set (Point n) :=
  {x | ¬ ∀ᶠ r in 𝓝[>] (0 : ℝ), oscillationAverage f hf r x ≤ 3 * ε}

lemma badOscillation_subset (f g : Point n → 𝕜) (hf : locallyIntegrable f)
    (hg : locallyIntegrable g) (hc : Continuous g)
    (he : locallyIntegrable (fun y => f y - g y)) (ε : ℝ) (hε : 0 < ε) :
    badOscillation f hf ε ⊆
      {x | ENNReal.ofReal ε < maximal (fun y => f y - g y) he x} ∪
      {x | ε < ‖f x - g x‖} := by
  intro x hx
  by_contra hnot
  have hsmall := not_or.mp hnot
  have hmax : maximal (fun y => f y - g y) he x ≤ ENNReal.ofReal ε :=
    le_of_not_gt hsmall.1
  have herr : ‖f x - g x‖ ≤ ε := le_of_not_gt hsmall.2
  have hgc := (tendsto_order.mp (continuous_lebesguePoint g hg (hc.continuousAt (x := x)))).2 ε hε
  apply hx
  filter_upwards [hgc, self_mem_nhdsWithin] with r hgr hr
  have ha : absoluteAverage (fun y => f y - g y) he r x ≤ ε := by
    have hb : ENNReal.ofReal (absoluteAverage (fun y => f y - g y) he r x) ≤
        ENNReal.ofReal ε :=
      (le_iSup₂ (f := fun (r : ℝ) (_ : 0 < r) =>
        ENNReal.ofReal (absoluteAverage (fun y => f y - g y) he r x)) r hr).trans hmax
    exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hb
  exact (oscillation_comparison f g hf hg he x r hr).trans (by linarith)

lemma badOscillation_null_of_integrable (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (lebesgue n)) (ε : ℝ) (hε : 0 < ε) :
    lebesgue n (badOscillation f hf ε) = 0 := by
  let C : ℝ≥0∞ := ((3 : ℝ≥0∞)^n + 1) * (ENNReal.ofReal ε)⁻¹
  have hC : C ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top ENNReal.ofNat_ne_top, by simp⟩
    · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hε).ne'
  have hb (k : ℕ) : lebesgue n (badOscillation f hf ε) ≤
      C * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    obtain ⟨g, hgi, herr⟩ := exists_cc_integral_lt f hi
      (show 0 < 1 / ((k : ℝ) + 1) by positivity)
    have hgm : Measurable (g : Point n → 𝕜) := g.continuous.measurable
    have hg := locallyIntegrable_of_integrable (g : Point n → 𝕜) hgm hgi
    have hem : Measurable (fun y => f y - g y) := hf.1.sub hgm
    have hei : Integrable (fun y => f y - g y) (lebesgue n) := hi.sub hgi
    have he := locallyIntegrable_of_integrable _ hem hei
    calc
      _ ≤ lebesgue n ({x | ENNReal.ofReal ε < maximal (fun y => f y - g y) he x} ∪
          {x | ε < ‖f x - g x‖}) :=
        measure_mono (badOscillation_subset f g hf hg g.continuous he ε hε)
      _ ≤ _ := measure_union_le _ _
      _ ≤ (3 : ℝ≥0∞)^n * (ENNReal.ofReal ε)⁻¹ *
          ENNReal.ofReal (∫ y, ‖f y - g y‖ ∂(lebesgue n)) +
          (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal (∫ y, ‖f y - g y‖ ∂(lebesgue n)) :=
        add_le_add (maximal_weak11 _ he hei ε hε) (error_level_bound _ hem hei ε hε)
      _ = C * ENNReal.ofReal (∫ y, ‖f y - g y‖ ∂(lebesgue n)) := by
        simp only [C, add_mul, one_mul, mul_assoc]
      _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal herr.le) C
  have ht : Tendsto (fun k : ℕ => C * ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, mul_zero] using ENNReal.Tendsto.const_mul
      (a := C) (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat) (Or.inr hC)
  exact le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) zero_le

/-- Global L1 differentiation, proved only from Cc density and weak (1,1). -/
theorem ae_lebesguePoint_of_integrable (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hi : Integrable f (lebesgue n)) : ∀ᵐ x ∂(lebesgue n), lebesguePoint f hf x := by
  have hall : ∀ k : ℕ, ∀ᵐ x ∂(lebesgue n),
      ∀ᶠ r in 𝓝[>] (0 : ℝ), oscillationAverage f hf r x ≤ 3 * (1 / ((k : ℝ) + 1)) := by
    intro k
    exact ae_iff.mpr (badOscillation_null_of_integrable f hf hi _ (by positivity))
  filter_upwards [ae_all_iff.mpr hall] with x hx
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun r => ha.trans_le (oscillation_nonneg f hf r x))
  · intro a ha
    have ht : Tendsto (fun k : ℕ => 3 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (3 : ℝ)
    obtain ⟨k, hk⟩ := ((tendsto_order.mp ht).2 a ha).exists
    exact (hx k).mono (fun r hr => hr.trans_lt hk)

/-- The Lebesgue-point property only uses the function near the point. -/
lemma lebesguePoint_congr_nhds (f g : Point n → 𝕜) (hf : locallyIntegrable f)
    (hg : locallyIntegrable g) {x : Point n} (hfg : f =ᶠ[𝓝 x] g)
    (h : lebesguePoint g hg x) : lebesguePoint f hf x := by
  have hx : f x = g x := hfg.self_of_nhds
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hfg
  apply h.congr'
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with r hr
  rw [oscillation_eq_setAverage, oscillation_eq_setAverage]
  apply setAverage_congr_fun (ball_measurable x r)
  filter_upwards with y hy
  rw [hball (ball_subset_ball hr.le hy), hx]

/-- Local L1 is sufficient: truncate on the countable open-ball exhaustion. -/
theorem ae_lebesguePoint (f : Point n → 𝕜) (hf : locallyIntegrable f) :
    ∀ᵐ x ∂(lebesgue n), lebesguePoint f hf x := by
  let fN (k : ℕ) : Point n → 𝕜 := (ball 0 ((k : ℝ) + 1)).indicator f
  have hi (k : ℕ) : Integrable (fN k) (lebesgue n) :=
    (integrable_indicator_iff (ball_measurable _ _)).mpr (integrableOn_ball f hf _ _)
  have hm (k : ℕ) : Measurable (fN k) := hf.1.indicator (ball_measurable _ _)
  have hloc (k : ℕ) := locallyIntegrable_of_integrable (fN k) (hm k) (hi k)
  have hN : ∀ k : ℕ, ∀ᵐ x ∂(lebesgue n), lebesguePoint (fN k) (hloc k) x :=
    fun k => ae_lebesguePoint_of_integrable (fN k) (hloc k) (hi k)
  filter_upwards [ae_all_iff.mpr hN] with x hx
  obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
  have hxball : x ∈ ball (0 : Point n) ((k : ℝ) + 1) := by
    simpa only [mem_ball, dist_zero_right] using (show ‖x‖ < (k : ℝ) + 1 by linarith)
  apply lebesguePoint_congr_nhds f (fN k) hf (hloc k) _ (hx k)
  filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
  exact (indicator_of_mem hy f).symm

/-- Scalar average error is bounded by the average absolute error. -/
lemma norm_average_sub_le (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (x z : Point n) (r : ℝ) (hr : 0 < r) :
    ‖average f hf r z - f x‖ ≤
      (lebesgue n (ball z r)).toReal⁻¹ * ∫ y in ball z r, ‖f y - f x‖ ∂(lebesgue n) := by
  have hm := ball_measure z r hr
  have hi := integrableOn_ball f hf z r
  rw [average_eq_setAverage]
  nth_rw 1 [← setAverage_const hm.1.ne' hm.2.1.ne (f x)]
  rw [← setAverage_sub hi (integrableOn_const hm.2.1.ne), setAverage_eq]
  rw [norm_smul, Real.norm_eq_abs, measureReal_def,
    abs_of_nonneg (inv_nonneg.mpr (ENNReal.toReal_nonneg (a := lebesgue n (ball z r))))]
  simp only [Pi.sub_apply]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)

lemma average_tendsto_of_lebesguePoint (f : Point n → 𝕜) (hf : locallyIntegrable f)
    {x : Point n} (hx : lebesguePoint f hf x) :
    Tendsto (fun r => average f hf r x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun r => norm_nonneg _)) _ hx
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact norm_average_sub_le f hf x x r hr

/-- Containing balls have uniformly comparable volume to a centered ball.
The harmless factor 3 uses the previously proved dilation formula. -/
lemma containing_ball_oscillation_le (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (x z : Point n) (r : ℝ) (hr : 0 < r) (hx : x ∈ ball z r) :
    (lebesgue n (ball z r)).toReal⁻¹ * ∫ y in ball z r, ‖f y - f x‖ ∂(lebesgue n) ≤
      (3 : ℝ)^n * oscillationAverage f hf (3 * r) x := by
  have hsub : ball z r ⊆ ball x (3 * r) := by
    intro y hy
    have hxy := dist_triangle y z x
    have hzx : dist z x < r := by simpa only [mem_ball, dist_comm] using hx
    change dist y z < r at hy
    change dist y x < 3 * r
    linarith
  have hi := integrableOn_ball (fun y => ‖f y - f x‖)
    (locallyIntegrable_norm _ (locallyIntegrable_sub_const f hf (f x))) x (3 * r)
  have hb := setIntegral_mono_set hi (ae_of_all _ (fun y => norm_nonneg (f y - f x)))
    (ae_of_all (lebesgue n) (fun y => hsub (a := y)))
  have hscale := D11.Ch13.FiniteBallCovering.lebesgue_ball_triple n x r
  change lebesgue n (ball x (3 * r)) = (3 : ℝ≥0∞)^n * lebesgue n (ball x r) at hscale
  have hm : (lebesgue n (ball x (3 * r))).toReal =
      (3 : ℝ)^n * (lebesgue n (ball z r)).toReal := by
    rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_pow,
      lebesgue_ball_center x r, lebesgue_ball_center z r]
    norm_num
  have hpos := (ball_measure z r hr).2.2
  have hc : (3 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  change _ ≤ (3 : ℝ)^n * ((lebesgue n (ball x (3 * r))).toReal⁻¹ * _)
  rw [hm]
  have hs := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpos.le)
  convert hs using 1 <;> field_simp
  rfl

/-- At each Lebesgue point, every filtered family of containing balls
converges, for both the absolute oscillations and the scalar averages. -/
theorem containing_balls_tendsto (f : Point n → 𝕜) (hf : locallyIntegrable f)
    {x : Point n} (hx : lebesguePoint f hf x)
    {ι : Type u} {l : Filter ι} (z : ι → Point n) (r : ι → ℝ)
    (hr : Tendsto r l (𝓝[>] (0 : ℝ)))
    (hxball : ∀ᶠ i in l, x ∈ ball (z i) (r i)) :
    Tendsto (fun i => (lebesgue n (ball (z i) (r i))).toReal⁻¹ *
      ∫ y in ball (z i) (r i), ‖f y - f x‖ ∂(lebesgue n)) l (𝓝 0) ∧
    Tendsto (fun i => average f hf (r i) (z i)) l (𝓝 (f x)) := by
  have hpos : ∀ᶠ i in l, 0 < r i := hr self_mem_nhdsWithin
  have htr : Tendsto (fun i => 3 * r i) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hpos.mono (fun i hi => by change 0 < 3 * r i; positivity)⟩
    simpa using (tendsto_nhds_of_tendsto_nhdsWithin hr).const_mul (3 : ℝ)
  have hlim : Tendsto (fun i => (3 : ℝ)^n * oscillationAverage f hf (3 * r i) x) l (𝓝 0) := by
    simpa using (hx.comp htr).const_mul ((3 : ℝ)^n)
  have hosc : Tendsto (fun i => (lebesgue n (ball (z i) (r i))).toReal⁻¹ *
      ∫ y in ball (z i) (r i), ‖f y - f x‖ ∂(lebesgue n)) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun i => mul_nonneg (by positivity)
      (integral_nonneg (fun y => norm_nonneg _)))) _ hlim
    filter_upwards [hpos, hxball] with i hi hxi
    exact containing_ball_oscillation_le f hf x (z i) (r i) hi hxi
  refine ⟨hosc, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun i => norm_nonneg _)) _ hosc
  exact hpos.mono (fun i hi => norm_average_sub_le f hf x (z i) (r i) hi)

/-- In positive-dimensional Euclidean space shrinking ball diameters
force their radii to shrink. Containment ensures eventual positivity. -/
lemma radii_tendsto_of_diam_tendsto {x : Point n} {ι : Type u} {l : Filter ι}
    (z : ι → Point n) (r : ι → ℝ)
    (hd : Tendsto (fun i => diam (ball (z i) (r i))) l (𝓝 (0 : ℝ)))
    (hx : ∀ᶠ i in l, x ∈ ball (z i) (r i)) :
    Tendsto r l (𝓝[>] (0 : ℝ)) := by
  have hp : ∀ᶠ i in l, 0 < r i := hx.mono (fun i hi => nonempty_ball.mp ⟨x, hi⟩)
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, hp⟩
  have ht := hd.div_const (2 : ℝ)
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [hp] with i hi
  rw [Metric.diam_ball_eq (z i) hi.le]
  ring

/-- Lebesgue differentiation for the fixed measurable representative,
including all containing-ball families outside one completed null set. -/
theorem lebesgue_differentiation :
    Specs.D11.Ch13.LebesgueDifferentiation.lebesgue_differentiation.{u} := by
  intro n _ 𝕜 _ _ _ f hf
  change locallyIntegrable f at hf
  obtain ⟨N, hsub, hN, hnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp (ae_lebesguePoint f hf))
  refine ⟨N, hN, hnull, ?_⟩
  intro x hx
  have hp : lebesguePoint f hf x := by
    by_contra h
    exact hx (hsub h)
  refine ⟨hp, average_tendsto_of_lebesguePoint f hf hp, ?_⟩
  intro ι l z r hr hxball
  exact containing_balls_tendsto f hf hp z r
    (radii_tendsto_of_diam_tendsto z r hr hxball) hxball

end D11.Ch13.LebesgueDifferentiation
