import MathGenome.Internal.FourierSobolev.P102.U2.Young
import MathGenome.Internal.FourierSobolev.Specs.P102.U2.ApproximateIdentities
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology ENNReal

namespace P102.U2.ApproximateIdentities
open ApproximateIdentitiesExpected

section SplitEstimate
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure X}

/-- A near/far estimate that uses absolute kernel mass, so applies to complex
and signed kernels. No positivity of the kernel is needed. -/
lemma norm_integral_le_near_add_tail {w : X → ℝ} (hw : Integrable w μ)
    (hw0 : ∀ y, 0 ≤ w y) {s : Set X} (hs : MeasurableSet s)
    {F : X → E} {a B : ℝ} (ha : 0 ≤ a)
    (hnear : ∀ y ∈ s, ‖F y‖ ≤ w y * a)
    (hbound : ∀ y, ‖F y‖ ≤ w y * B) :
    ‖∫ y, F y ∂μ‖ ≤ a * (∫ y, w y ∂μ) + B * ∫ y in sᶜ, w y ∂μ := by
  have hi := (hw.mul_const a).add ((hw.mul_const B).indicator hs.compl)
  calc
    _ ≤ ∫ y, w y * a + sᶜ.indicator (fun y => w y * B) y ∂μ := by
      apply norm_integral_le_of_norm_le hi
      apply Eventually.of_forall
      intro y
      by_cases hy : y ∈ s
      · simpa [hy] using hnear y hy
      · simpa [hy] using (hbound y).trans (le_add_of_nonneg_left (mul_nonneg (hw0 y) ha))
    _ = _ := by
      rw [integral_add (hw.mul_const a) ((hw.mul_const B).indicator hs.compl),
        integral_indicator hs.compl, integral_mul_const, integral_mul_const]
      ring

end SplitEstimate

section Uniform
variable {G 𝕜 : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [RCLike 𝕜]
    (μ : Measure G) [IsAddLeftInvariant μ] [IsNegInvariant μ]
    [MeasurableAdd₂ G] [MeasurableNeg G]

/-- Change variables y ↦ x-y. This is also the bridge between the canonical
source order and the kernel-weighted translation formula. -/
lemma convolution_swap (k f : G → 𝕜) (x : G) :
    (∫ y, k (x - y) * f y ∂μ) = ∫ y, k y * f (x - y) ∂μ := by
  rw [← integral_sub_left_eq_self (fun y => k (x - y) * f y) μ x]
  simp only [sub_sub_cancel]

lemma convolution_integrable_swap (k f : G → 𝕜) (x : G) :
    Integrable (fun y => k (x - y) * f y) μ ↔
      Integrable (fun y => k y * f (x - y)) μ := by
  simpa only [sub_sub_cancel] using
    (integrable_comp_sub_left (μ := μ) (fun y => k (x - y) * f y) x).symm

/-- Uniform recovery for the actual bounded uniformly continuous function.
The near part is controlled by uniform continuity, and the far part by 2M. -/
theorem uniform_recovery (k : ℝ → G → 𝕜) (hk : Conditions μ k) : UniformResult μ k := by
  intro f hf hfb
  obtain ⟨M, hM⟩ := hfb
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  obtain ⟨A, hA0, hA⟩ := hk.2.2.1
  have hi (ε : ℝ) (hε : 0 < ε) (x : G) :
      Integrable (fun y => k ε y * f (x - y)) μ :=
    (hk.1 ε hε).mul_bdd (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => hM (x - y))
  refine ⟨fun ε hε x => (convolution_integrable_swap μ _ _ _).mpr (hi ε hε x), ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro η hη
  let a := η / (2 * (A + 1))
  have ha : 0 < a := div_pos hη (by positivity)
  obtain ⟨r, hr, hfr⟩ := Metric.uniformContinuous_iff.mp hf a ha
  have htail := ((hk.2.2.2 (r / 2) (half_pos hr)).const_mul (2 * M))
  simp only [mul_zero] at htail
  have hev := (tendsto_order.mp htail).2 (η / 2) (half_pos hη)
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hεpos
  intro x
  have hε0 : 0 < ε := hεpos
  rw [dist_comm, dist_eq_norm, convolution_swap μ]
  have heq : (∫ y, k ε y * f (x - y) ∂μ) - f x =
      ∫ y, k ε y * (f (x - y) - f x) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub (hi ε hε0 x) ((hk.1 ε hε0).mul_const (f x)),
      integral_mul_const, hk.2.1 ε hε0, one_mul]
  rw [heq]
  have hlocal : ∀ y ∈ Metric.closedBall (0 : G) (r / 2),
      ‖k ε y * (f (x - y) - f x)‖ ≤ ‖k ε y‖ * a := by
    intro y hy
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply le_of_lt
    rw [← dist_eq_norm]
    apply hfr
    simpa [dist_eq_norm] using lt_of_le_of_lt hy (half_lt_self hr)
  have hb : ∀ y, ‖k ε y * (f (x - y) - f x)‖ ≤ ‖k ε y‖ * (2 * M) := by
    intro y
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hM (x - y), hM x])
  have hest := norm_integral_le_near_add_tail (hk.1 ε hε0).norm
    (fun y => norm_nonneg (k ε y)) Metric.isClosed_closedBall.measurableSet ha.le hlocal hb
  have hcompl : (Metric.closedBall (0 : G) (r / 2))ᶜ =
      {y : G | r / 2 < dist y 0} := by ext y; simp
  rw [hcompl] at hest
  apply hest.trans_lt
  have hna : a * (∫ y, ‖k ε y‖ ∂μ) ≤ a * A :=
    mul_le_mul_of_nonneg_left (hA ε hε0) ha.le
  have hsmall : a * A < η / 2 := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (A + 1))).mpr
    nlinarith
  linarith

end Uniform

theorem euclidean_uniform : EuclideanUniform := by
  intro d _hd 𝕜 _ k hk
  exact uniform_recovery volume k hk

theorem circle_uniform : CircleUniform := by
  intro T _ 𝕜 _ k hk
  exact uniform_recovery (Periodic.haar T) k hk

section Translations
variable {G E : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [NormedAddCommGroup E]
    (μ : Measure G) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [IsAddRightInvariant μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def translate (y : G) (f : Lp E p μ) : Lp E p μ :=
  Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right μ y) f

lemma translate_ae (y : G) (f : Lp E p μ) :
    translate μ y f =ᵐ[μ] fun x => f (x - y) :=
  Lp.coeFn_compMeasurePreserving _ _

@[simp] lemma norm_translate (y : G) (f : Lp E p μ) : ‖translate μ y f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

@[simp] lemma translate_zero (f : Lp E p μ) : translate μ 0 f = f := by
  unfold translate
  simp only [sub_zero]
  exact Lp.compMeasurePreserving_id_apply f

/-- Strong continuity of translations in each finite Lp space. -/
theorem continuous_translate (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous (fun y => translate μ y f) := by
  let shifts : C(G, C(G, G)) :=
    (⟨fun z : G × G => z.2 - z.1, continuous_snd.sub continuous_fst⟩ : C(G × G, G)).curry
  exact continuous_const.compMeasurePreservingLp shifts.continuous
    (fun y => measurePreserving_sub_right μ y) hp

theorem translation_norm_tendsto (hp : p ≠ ∞) {f : G → E} (hf : MemLp f p μ) :
    Tendsto (fun y => eLpNorm (fun x => f (x - y) - f x) p μ) (𝓝 0) (𝓝 0) := by
  have ht := (continuous_translate μ hp (hf.toLp f)).tendsto 0
  rw [translate_zero] at ht
  have h := ht.edist (tendsto_const_nhds (x := hf.toLp f))
  simp only [edist_self] at h
  convert h using 1
  funext y
  rw [Lp.edist_def]
  apply eLpNorm_congr_ae
  exact ((translate_ae μ y (hf.toLp f)).trans
    ((measurePreserving_sub_right μ y).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp )).sub hf.coeFn_toLp |>.symm

end Translations

section IntegralLp
variable {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A finite-set integral is a continuous linear functional on Lp. -/
lemma integral_norm_le_lp (s : Set X) (hs : μ s ≠ ∞) (f : Lp 𝕜 p μ) :
    (∫ x in s, ‖f x‖ ∂μ) ≤ ‖f‖ * (μ s ^ (1 - 1 / p.toReal)).toReal := by
  have hi := integrableOn_Lp_of_measure_ne_top f (Fact.out : 1 ≤ p) hs
  have h1 : eLpNorm f 1 (μ.restrict s) ≤
      eLpNorm f p μ * μ s ^ (1 - 1 / p.toReal) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Fact.out : 1 ≤ p)
      ((Lp.aestronglyMeasurable f).restrict (s := s))
    simp only [ENNReal.toReal_one, div_one, Measure.restrict_apply_univ] at h
    exact h.trans (mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) le_rfl)
  have hfinite : eLpNorm f p μ * μ s ^ (1 - 1 / p.toReal) ≠ ∞ :=
    (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top f)
      (ENNReal.rpow_lt_top_of_nonneg (by
        have hp := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞)
          (show p⁻¹ ≤ 1 from ENNReal.inv_le_one.mpr Fact.out)
        simpa using sub_nonneg.mpr hp) hs)).ne
  have heq : (eLpNorm f 1 (μ.restrict s)).toReal = ∫ x in s, ‖f x‖ ∂μ := by
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  rw [← heq, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hfinite h1

def setIntegralLp (s : Set X) (hs : μ s ≠ ∞) : Lp 𝕜 p μ →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x in s, f x ∂μ
      map_add' := fun f g => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))]
        exact integral_add (integrableOn_Lp_of_measure_ne_top f Fact.out hs)
          (integrableOn_Lp_of_measure_ne_top g Fact.out hs)
      map_smul' := fun c f => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))]
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
    (μ s ^ (1 - 1 / p.toReal)).toReal (fun f => by
      exact (norm_integral_le_integral_norm _).trans
        (by simpa [mul_comm] using integral_norm_le_lp μ s hs f))

end IntegralLp

section ConvolutionLp
variable {G 𝕜 : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [RCLike 𝕜]
    (μ : Measure G) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [SigmaFinite μ] [IsAddRightInvariant μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma integrable_weighted_translate (hp : p ≠ ∞) (f : Lp 𝕜 p μ)
    {k : G → 𝕜} (hk : Integrable k μ) :
    Integrable (fun y => k y • translate μ y f) μ := by
  refine (hk.norm.mul_const ‖f‖).mono' ?_ ?_
  · exact hk.aestronglyMeasurable.smul (continuous_translate μ hp f).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by simp [norm_smul]

/-- Fubini on a finite-measure test set. Its absolute integrability follows
from finite-set Hölder and the isometry of translations. -/
lemma integrable_convolution_on_set (f : Lp 𝕜 p μ) {k : G → 𝕜}
    (hk : Integrable k μ) (s : Set G) (hs : μ s ≠ ∞) :
    Integrable (fun z : G × G => k z.2 * f (z.1 - z.2)) ((μ.restrict s).prod μ) := by
  have hfull : AEStronglyMeasurable (fun z : G × G => k z.2 * f (z.1 - z.2)) (μ.prod μ) :=
    hk.aestronglyMeasurable.comp_snd.mul ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant μ μ))
  have hm : AEStronglyMeasurable (fun z : G × G => k z.2 * f (z.1 - z.2))
      ((μ.restrict s).prod μ) :=
    hfull.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  apply (integrable_prod_iff' hm).mpr
  refine ⟨Eventually.of_forall (fun y => ?_), ?_⟩
  · have ht := integrableOn_Lp_of_measure_ne_top (translate μ y f) (Fact.out : 1 ≤ p) hs
    have ht' : IntegrableOn (fun x => f (x - y)) s μ :=
      ht.congr (ae_restrict_of_ae (translate_ae μ y f))
    exact ht'.const_mul (k y)
  · refine (hk.norm.mul_const (‖f‖ * (μ s ^ (1 - 1 / p.toReal)).toReal)).mono'
      hm.norm.prod_swap.integral_prod_right' ?_
    apply Eventually.of_forall
    intro y
    have ht := integral_norm_le_lp μ s hs (translate μ y f)
    rw [norm_translate] at ht
    have heq : (∫ x in s, ‖translate μ y f x‖ ∂μ) =
        ∫ x in s, ‖f (x - y)‖ ∂μ :=
      integral_congr_ae (ae_restrict_of_ae ((translate_ae μ y f).fun_comp norm))
    rw [heq] at ht
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    simp only [norm_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

/-- The Bochner integral of weighted translations represents the canonical
scalar convolution. Finite-set integral functionals identify its Lp class. -/
theorem integral_translate_eq_convolution (hp : p ≠ ∞) (f : Lp 𝕜 p μ)
    {k : G → 𝕜} (hk : Integrable k μ) :
    (∫ y, k y • translate μ y f ∂μ) =
      ((Young.young μ (p := 1) (q := p) (r := p) (by simp : (1 : ℝ≥0∞) ≤ 1) Fact.out Fact.out (by simp)
        (memLp_one_iff_integrable.mpr hk) (Lp.memLp f)).2.1).toLp
        (Young.integralConvolution μ k f) := by
  let c := ((Young.young μ (p := 1) (q := p) (r := p) (by simp : (1 : ℝ≥0∞) ≤ 1) (Fact.out : 1 ≤ p) Fact.out (by simp)
    (memLp_one_iff_integrable.mpr hk) (Lp.memLp f)).2.1).toLp
      (Young.integralConvolution μ k f)
  let b : Lp 𝕜 p μ := ∫ y, k y • translate μ y f ∂μ
  have hi := integrable_weighted_translate μ hp f hk
  apply Lp.ext
  apply Lp.ae_eq_of_forall_setIntegral_eq b c
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ Fact.out hs.ne)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ Fact.out hs.ne)
  intro s hs hμs
  have heq (y : G) : (setIntegralLp μ s hμs.ne) (k y • translate μ y f) =
      ∫ x in s, k y * f (x - y) ∂μ := by
    rw [map_smul]
    change k y * (∫ x in s, translate μ y f x ∂μ) = _
    rw [integral_congr_ae (ae_restrict_of_ae (translate_ae μ y f)), integral_const_mul]
  calc
    (∫ x in s, b x ∂μ) = (setIntegralLp μ s hμs.ne) b := rfl
    _ = ∫ y, (setIntegralLp μ s hμs.ne) (k y • translate μ y f) ∂μ :=
      ((setIntegralLp μ s hμs.ne).integral_comp_comm hi).symm
    _ = ∫ y, ∫ x in s, k y * f (x - y) ∂μ ∂μ := by simp_rw [heq]
    _ = ∫ x in s, ∫ y, k y * f (x - y) ∂μ ∂μ :=
      (integral_integral_swap (integrable_convolution_on_set μ f hk s hμs.ne)).symm
    _ = ∫ x in s, c x ∂μ := by
      have hc : (c : G → 𝕜) =ᵐ[μ] Young.integralConvolution μ k f := MemLp.coeFn_toLp _
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hc] with x hx
      exact (convolution_swap μ k f x).symm.trans hx.symm

/-- Approximate identity convergence in the Banach space Lp, prior to
identifying its elements with the pointwise convolution formula. -/
theorem weighted_translate_tendsto (hp : p ≠ ∞) (f : Lp 𝕜 p μ)
    (k : ℝ → G → 𝕜) (hk : Conditions μ k) :
    Tendsto (fun ε => ∫ y, k ε y • translate μ y f ∂μ) (𝓝[>] 0) (𝓝 f) := by
  obtain ⟨A, hA0, hA⟩ := hk.2.2.1
  rw [Metric.tendsto_nhds]
  intro η hη
  let a := η / (2 * (A + 1))
  have ha : 0 < a := div_pos hη (by positivity)
  have ht : ContinuousAt (fun y => translate μ y f) 0 := (continuous_translate μ hp f).continuousAt
  obtain ⟨r, hr, hfr⟩ := Metric.continuousAt_iff.mp ht a ha
  simp only [translate_zero] at hfr
  have htail := ((hk.2.2.2 (r / 2) (half_pos hr)).const_mul (2 * ‖f‖))
  simp only [mul_zero] at htail
  filter_upwards [(tendsto_order.mp htail).2 (η / 2) (half_pos hη), self_mem_nhdsWithin]
    with ε hε hεpos
  have hε0 : 0 < ε := hεpos
  rw [dist_eq_norm]
  have heq : (∫ y, k ε y • translate μ y f ∂μ) - f =
      ∫ y, k ε y • (translate μ y f - f) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub (integrable_weighted_translate μ hp f (hk.1 ε hε0))
      ((hk.1 ε hε0).smul_const f), integral_smul_const, hk.2.1 ε hε0, one_smul]
  rw [heq]
  have hlocal : ∀ y ∈ Metric.closedBall (0 : G) (r / 2),
      ‖k ε y • (translate μ y f - f)‖ ≤ ‖k ε y‖ * a := by
    intro y hy
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← dist_eq_norm]
    exact (hfr (lt_of_le_of_lt hy (half_lt_self hr))).le
  have hb : ∀ y, ‖k ε y • (translate μ y f - f)‖ ≤ ‖k ε y‖ * (2 * ‖f‖) := by
    intro y
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by simp [two_mul])
  have hest := norm_integral_le_near_add_tail (hk.1 ε hε0).norm
    (fun y => norm_nonneg (k ε y)) Metric.isClosed_closedBall.measurableSet ha.le hlocal hb
  have hcompl : (Metric.closedBall (0 : G) (r / 2))ᶜ =
      {y : G | r / 2 < dist y 0} := by ext y; simp
  rw [hcompl] at hest
  apply hest.trans_lt
  have hna : a * (∫ y, ‖k ε y‖ ∂μ) ≤ a * A :=
    mul_le_mul_of_nonneg_left (hA ε hε0) ha.le
  have hsmall : a * A < η / 2 := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (A + 1))).mpr
    nlinarith
  linarith

theorem lp_recovery (k : ℝ → G → 𝕜) (hk : Conditions μ k) : LpResult μ k := by
  intro p hp hptop f hf
  let : Fact (1 ≤ p) := ⟨hp⟩
  have hY (ε : ℝ) (hε : 0 < ε) :=
    Young.young μ (p := 1) (q := p) (r := p) (by simp) hp hp (by simp)
      (memLp_one_iff_integrable.mpr (hk.1 ε hε)) hf
  refine ⟨fun ε hε => ⟨(hY ε hε).1, (hY ε hε).2.1⟩, ?_⟩
  have ht := weighted_translate_tendsto μ hptop (hf.toLp f) k hk
  have hn := ht.edist (tendsto_const_nhds (x := hf.toLp f))
  simp only [edist_self] at hn
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  have hε : 0 < ε := hεpos
  rw [integral_translate_eq_convolution μ hptop (hf.toLp f) (hk.1 ε hε), Lp.edist_def]
  apply eLpNorm_congr_ae
  have hconv : (Young.integralConvolution μ (k ε) (hf.toLp f)) =
      Young.integralConvolution μ (k ε) f :=
    Young.integralConvolution_congr μ ae_eq_rfl hf.coeFn_toLp
  exact ((MemLp.coeFn_toLp _).trans (Eventually.of_forall (congrFun hconv))).sub hf.coeFn_toLp

end ConvolutionLp

theorem euclidean_lp : EuclideanLp := by
  intro d _hd 𝕜 _ k hk
  exact lp_recovery volume k hk

theorem circle_lp : CircleLp := by
  intro T _ 𝕜 _ k hk
  exact lp_recovery (Periodic.haar T) k hk

section Completion
variable {G 𝕜 : Type*} [MeasurableSpace G] [RCLike 𝕜] (μ : Measure G)

lemma setIntegral_completion (s : Set G) (hs : MeasurableSet s) (f : G → 𝕜) :
    (∫ x : NullMeasurableSpace G μ in s, f x ∂μ.completion) = ∫ x in s, f x ∂μ := by
  have hsc : MeasurableSet (α := NullMeasurableSpace G μ) s := hs.nullMeasurableSet
  calc
    _ = ∫ x : NullMeasurableSpace G μ, s.indicator f x ∂μ.completion :=
      (integral_indicator (μ := μ.completion) hsc).symm
    _ = ∫ x, s.indicator f x ∂μ := Young.integral_completion μ (s.indicator f)
    _ = _ := integral_indicator hs

variable [NormedAddCommGroup G] [BorelSpace G]

lemma conditions_of_completed {k : ℝ → G → 𝕜} (hk : CompletedConditions μ k) :
    Conditions μ k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε hε
    exact memLp_one_iff_integrable.mp ((Periodic.mem_completion μ (k ε) 1).mp
      (memLp_one_iff_integrable.mpr (hk.1 ε hε)))
  · intro ε hε
    exact (Young.integral_completion μ (k ε)).symm.trans (hk.2.1 ε hε)
  · obtain ⟨A, hA, hAb⟩ := hk.2.2.1
    refine ⟨A, hA, fun ε hε => ?_⟩
    rw [← Young.integral_completion μ (fun y => ‖k ε y‖)]
    exact hAb ε hε
  · intro δ hδ
    convert hk.2.2.2 δ hδ using 1
    funext ε
    exact (setIntegral_completion μ _ (isOpen_lt continuous_const (continuous_id.dist
      continuous_const)).measurableSet (fun y => ‖k ε y‖)).symm

variable [SecondCountableTopology G] [IsAddLeftInvariant μ] [IsNegInvariant μ]
    [MeasurableAdd₂ G] [MeasurableNeg G]

theorem completed_uniform_recovery (k : ℝ → G → 𝕜) (hk : CompletedConditions μ k) :
    CompletedUniformResult μ k := by
  intro f hf hb
  have h := uniform_recovery μ k (conditions_of_completed μ hk) f hf hb
  have hc (ε : ℝ) (x : G) :
      (∫ y : NullMeasurableSpace G μ, k ε (@Sub.sub G _ x y) * f y ∂μ.completion) =
      ∫ y, k ε (x - y) * f y ∂μ := Young.integral_completion μ _
  refine ⟨?_, ?_⟩
  · intro ε hε x
    exact memLp_one_iff_integrable.mp ((Periodic.mem_completion μ _ 1).mpr
      (memLp_one_iff_integrable.mpr (h.1 ε hε x)))
  · simpa only [hc] using h.2

variable [LocallyCompactSpace G] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [SigmaFinite μ] [IsAddRightInvariant μ]

theorem completed_lp_recovery (k : ℝ → G → 𝕜) (hk : CompletedConditions μ k) :
    CompletedLpResult μ k := by
  intro p hp hptop f hf
  have hk' := conditions_of_completed μ hk
  have hf' := (Periodic.mem_completion μ f p).mp hf
  have h := lp_recovery μ k hk' p hp hptop f hf'
  have hc (ε : ℝ) (x : G) :
      (∫ y : NullMeasurableSpace G μ, k ε (@Sub.sub G _ x y) * f y ∂μ.completion) =
      ∫ y, k ε (x - y) * f y ∂μ := Young.integral_completion μ _
  refine ⟨?_, ?_⟩
  · intro ε hε
    have hY := Young.young_completed μ (p := 1) (q := p) (r := p) (by simp) hp hp
      (by simp) (memLp_one_iff_integrable.mpr (hk.1 ε hε)) hf
    exact ⟨hY.1, hY.2.1⟩
  · apply h.2.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hεpos
    have hε : 0 < ε := hεpos
    have heq :
        (fun x : NullMeasurableSpace G μ =>
          (∫ y : NullMeasurableSpace G μ, k ε (@Sub.sub G _ x y) * f y ∂μ.completion) - f x) =
        (fun x : NullMeasurableSpace G μ =>
          (∫ y : G, k ε (@Sub.sub G _ x y) * f y ∂μ) - f x) := by
      funext x
      exact congrArg (fun z => z - f x) (hc ε x)
    have hn := congrArg (fun g : NullMeasurableSpace G μ → 𝕜 => eLpNorm g p μ.completion) heq
    exact (Periodic.norm_completion μ _ p ((h.1 ε hε).2.aestronglyMeasurable.sub
      hf'.aestronglyMeasurable)).symm.trans hn.symm

end Completion

theorem euclidean_completed_uniform : EuclideanCompletedUniform := by
  intro d _hd 𝕜 _ k hk
  exact completed_uniform_recovery volume k hk

theorem circle_completed_uniform : CircleCompletedUniform := by
  intro T _ 𝕜 _ k hk
  exact completed_uniform_recovery (Periodic.haar T) k hk

theorem euclidean_completed_lp : EuclideanCompletedLp := by
  intro d _hd 𝕜 _ k hk
  exact completed_lp_recovery volume k hk

theorem circle_completed_lp : CircleCompletedLp := by
  intro T _ 𝕜 _ k hk
  exact completed_lp_recovery (Periodic.haar T) k hk

end P102.U2.ApproximateIdentities
