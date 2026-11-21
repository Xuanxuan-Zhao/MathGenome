import MathGenome.Internal.FourierSobolev.Specs.P102.U2.MaximalStrong
import MathGenome.Internal.FourierSobolev.P102.U2.MaximalWeak
import MathGenome.Internal.RealAnalysis.D11.Ch11.ConvolutionBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.MaximalStrongBoundsAndDifferentiation
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace P102.U2.MaximalStrong
open D11.Ch03 D11.Ch03.LebesgueMeasures D11.Ch03.EuclideanRegularity
open D11.Ch13.AveragesMaximalDefinition
open ExpandedFA.Interpolation.MarcinkiewiczSpec
open MaximalWeak MaximalStrongSpec
section Completed
local instance (d : ℕ) [NeZero d] : MeasurableSpace (Point d) := lebesgueSpace d
variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

theorem localIntegrability : MaximalStrongSpec.LocalIntegrability := by
  intro d _ 𝕜 _ _ _ p hp f hf
  change MemLp f p (μ d) at hf
  let : (μ d).IsComplete := lebesgue_complete d
  apply (locallyIntegrable_iff f).mpr
  refine ⟨aemeasurable_iff_measurable.mp hf.aemeasurable, ?_⟩
  intro K hK
  have : IsFiniteMeasure ((μ d).restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact (hf.restrict K).integrable hp

theorem sumDomain_local : MaximalStrongSpec.SumDomainLocal := by
  intro d _ 𝕜 _ _ _ f hf
  change sumDomain (μ d) 1 ∞ f at hf
  obtain ⟨g, h, hg, hh, he⟩ := hf
  have hgl := (locallyIntegrable_iff g).mp (localIntegrability 1 le_rfl g hg)
  have hhl := (locallyIntegrable_iff h).mp (localIntegrability ∞ le_top h hh)
  let : (μ d).IsComplete := lebesgue_complete d
  apply (locallyIntegrable_iff f).mpr
  refine ⟨aemeasurable_iff_measurable.mp ((hg.aestronglyMeasurable.add
    hh.aestronglyMeasurable).congr he.symm).aemeasurable, ?_⟩
  intro K hK
  exact ((hgl.2 K hK).add (hhl.2 K hK)).congr (ae_restrict_of_ae he.symm)

lemma ballAverage_add_le (f g : Point d → 𝕜)
    (hf : locallyIntegrable f) (hg : locallyIntegrable g) (r : ℝ) (x : Point d) :
    ballAverage (f + g) r x ≤ ballAverage f r x + ballAverage g r x := by
  have hi (f : Point d → 𝕜) (hf : locallyIntegrable f) :
      IntegrableOn f (ball x r) (μ d) :=
    (((locallyIntegrable_iff f).mp hf).2 _ (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall
  unfold ballAverage
  rw [← mul_add, ← integral_add (hi f hf).norm (hi g hg).norm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact integral_mono ((hi f hf).add (hi g hg)).norm
    ((hi f hf).norm.add (hi g hg).norm) (fun y => norm_add_le _ _)

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
lemma ballAverage_smul (c : 𝕜) (f : Point d → 𝕜) (r : ℝ) (x : Point d) :
    ballAverage (c • f) r x = ‖c‖ * ballAverage f r x := by
  simp only [ballAverage, Pi.smul_apply, norm_smul, integral_const_mul]
  ring

lemma maximal_add_le (b : Bool) (f g : Point d → 𝕜)
    (hf : locallyIntegrable f) (hg : locallyIntegrable g) (x : Point d) :
    maximalValue b (f + g) x ≤ maximalValue b f x + maximalValue b g x := by
  have havg (r : ℝ) (z : Point d) :
      ENNReal.ofReal (ballAverage (f + g) r z) ≤
        ENNReal.ofReal (ballAverage f r z) + ENNReal.ofReal (ballAverage g r z) := by
    exact (ENNReal.ofReal_le_ofReal (ballAverage_add_le f g hf hg r z)).trans_eq
      (ENNReal.ofReal_add (by exact mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _)))
        (by exact mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))))
  cases b
  · change centered (f + g) x ≤ centered f x + centered g x
    exact iSup_le fun r => iSup_le fun hr => (havg r x).trans
      (add_le_add (le_iSup₂_of_le r hr le_rfl) (le_iSup₂_of_le r hr le_rfl))
  · change uncentered (f + g) x ≤ uncentered f x + uncentered g x
    exact iSup_le fun z => iSup_le fun r => iSup_le fun hr => iSup_le fun hx =>
      (havg r z).trans (add_le_add
        (le_iSup_of_le z (le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le hx le_rfl))))
        (le_iSup_of_le z (le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le hx le_rfl)))))

lemma maximal_smul (b : Bool) (c : 𝕜) (f : Point d → 𝕜) (x : Point d) :
    maximalValue b (c • f) x = ENNReal.ofReal ‖c‖ * maximalValue b f x := by
  have havg (r : ℝ) (z : Point d) : ENNReal.ofReal (ballAverage (c • f) r z) =
      ENNReal.ofReal ‖c‖ * ENNReal.ofReal (ballAverage f r z) := by
    rw [ballAverage_smul, ENNReal.ofReal_mul (norm_nonneg _)]
  cases b
  · change centered (c • f) x = ENNReal.ofReal ‖c‖ * centered f x
    simp_rw [centered, havg, ENNReal.mul_iSup]
  · change uncentered (c • f) x = ENNReal.ofReal ‖c‖ * uncentered f x
    simp_rw [uncentered, havg, ENNReal.mul_iSup]

theorem sublinear : MaximalStrongSpec.SublinearAction := by
  intro d _ 𝕜 _ _ _ b f hf
  have hm := MaximalWeak.measurable_maximal f hf
  refine ⟨?_, ?_, fun g hg x => maximal_add_le b f g hf hg x, fun c x => maximal_smul b c f x⟩
  · cases b
    · exact hm.1
    · exact hm.2
  · intro g hg he
    have h := MaximalWeak.ae_invariant f g hf hg he
    cases b <;> first | exact h.1 | exact h.2
end Completed

section Borel
abbrev borelVolume (d : ℕ) : Measure (Point d) := volume
variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Trimming the completed measure preserves the norm of a Borel version. -/
lemma borel_norm_eq (p : ℝ≥0∞) (f : Point d → 𝕜) (hf : Measurable f) :
    eLpNorm f p volume = eLpNorm f p (μ d) := by
  have h := eLpNorm_trim (μ := μ d) (p := p) (native_borel_le d) hf.stronglyMeasurable
  have htrim : (μ d).trim (native_borel_le d) = borelVolume d :=
    borel_restriction d (native_borel_le d)
  rw [htrim] at h
  exact h

lemma borel_average_eq (f : Point d → 𝕜) (hf : Measurable f) (r : ℝ) (x : Point d) :
    ballAverage f r x = (volume (ball x r)).toReal⁻¹ * ∫ y in ball x r, ‖f y‖ := by
  unfold ballAverage
  rw [lebesgue_eq_volume]
  congr 1
  have h := setIntegral_trim (μ := μ d) (native_borel_le d)
    hf.stronglyMeasurable.norm (s := ball x r) measurableSet_ball
  have htrim : (μ d).trim (native_borel_le d) = borelVolume d :=
    borel_restriction d (native_borel_le d)
  rw [htrim] at h
  exact h

lemma centered_eq_borel (f : Point d → 𝕜) (hf : Measurable f)
    (hl : LocallyIntegrable f volume) :
    centered f = ExpandedFA.SingularIntegrals.centeredMaximal volume f := by
  funext x
  have h := ExpandedFA.SingularIntegrals.centeredMaximal_ballIntegral d f hl x
  change ExpandedFA.SingularIntegrals.centeredMaximal volume f x = _ at h
  rw [h]
  unfold centered
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  rw [borel_average_eq f hf r x]
  rfl

/-- The extended moment transfers through the Borel restriction, too. -/
lemma centered_moment_eq_borel (f : Point d → 𝕜) (hf : Measurable f)
    (hl : LocallyIntegrable f volume) (p : ℝ) :
    (∫⁻ x, centered f x ^ p ∂(μ d)) =
      ∫⁻ x, ExpandedFA.SingularIntegrals.centeredMaximal volume f x ^ p := by
  rw [centered_eq_borel f hf hl]
  have hm := (ExpandedFA.SingularIntegrals.centeredMaximal_measurable d f).pow_const p
  have h := lintegral_trim (μ := μ d) (native_borel_le d) hm
  have htrim : (μ d).trim (native_borel_le d) = borelVolume d :=
    borel_restriction d (native_borel_le d)
  rw [htrim] at h
  exact h.symm
lemma centered_moment_eq_borel_of_memLp (f : Point d → 𝕜) (hf : Measurable f)
    (p : ℝ) (hp : 1 ≤ ENNReal.ofReal p) (hLp : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, centered f x ^ p ∂(μ d)) =
      ∫⁻ x, ExpandedFA.SingularIntegrals.centeredMaximal volume f x ^ p :=
  centered_moment_eq_borel f hf (hLp.locallyIntegrable hp) p
end Borel

section Completed
local instance (d : ℕ) [NeZero d] : MeasurableSpace (Point d) := lebesgueSpace d
variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

lemma centered_finite_bound (p : ℝ) (hp : 1 < p) : ∃ C : ℝ≥0,
    ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
      (f : Point d → 𝕜), MemLp f (ENNReal.ofReal p) (μ d) →
      (∫⁻ x, centered f x ^ p ∂(μ d)) ^ (1 / p) ≤
        (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (μ d) := by
  obtain ⟨C, hC⟩ := ExpandedFA.SingularIntegrals.centeredMaximal_strong_finite d p hp
  refine ⟨C, ?_⟩
  intro 𝕜 _ _ _ f hf
  let : (μ d).IsComplete := lebesgue_complete d
  have hfm : Measurable f := aemeasurable_iff_measurable.mp hf.aemeasurable
  obtain ⟨g, hg, hfg⟩ := D11.Ch11.ConvolutionBound.borel_version f hfm
  change f =ᵐ[μ d] g at hfg
  have hn := borel_norm_eq (ENNReal.ofReal p) g hg
  have hgLp : MemLp g (ENNReal.ofReal p) (μ d) := hf.ae_eq hfg
  have hgB : MemLp g (ENNReal.ofReal p) (borelVolume d) := by
    rw [memLp_iff, hn]
    exact hgLp
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have he := (MaximalWeak.ae_invariant f g (localIntegrability _ hp1 f hf)
    (localIntegrability _ hp1 g hgLp) hfg).1
  change centered f = centered g at he
  rw [he, centered_moment_eq_borel_of_memLp g hg p hp1 hgB]
  have h := hC g hgB
  rw [hn, ← eLpNorm_congr_ae hfg] at h
  exact h

lemma ofReal_ballAverage_eq (f : Point d → 𝕜) (hf : locallyIntegrable f)
    (r : ℝ) (hr : 0 < r) (x : Point d) :
    ENNReal.ofReal (ballAverage f r x) =
      (∫⁻ y in ball x r, ‖f y‖ₑ ∂(μ d)) / μ d (ball x r) := by
  have hi : IntegrableOn f (ball x r) (μ d) :=
    (((locallyIntegrable_iff f).mp hf).2 _ (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall
  rw [ballAverage, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_inv_of_pos (ball_measure x r hr).2.2,
    ENNReal.ofReal_toReal (ball_measure x r hr).2.1.ne,
    ofReal_integral_norm_eq_lintegral_enorm hi]
  exact ENNReal.div_eq_inv_mul.symm

lemma ballAverage_le_infinity (f : Point d → 𝕜) (hf : MemLp f ∞ (μ d))
    (r : ℝ) (hr : 0 < r) (x : Point d) :
    ENNReal.ofReal (ballAverage f r x) ≤ eLpNorm f ∞ (μ d) := by
  rw [ofReal_ballAverage_eq f (localIntegrability ∞ le_top f hf) r hr x]
  apply (ENNReal.div_le_iff (ball_measure x r hr).1.ne'
    (ball_measure x r hr).2.1.ne).mpr
  calc
    (∫⁻ y in ball x r, ‖f y‖ₑ ∂(μ d)) ≤
        ∫⁻ _y in ball x r, eLpNorm f ∞ (μ d) ∂(μ d) := by
      apply lintegral_mono_ae
      apply ae_restrict_of_ae
      simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using
        (ae_le_eLpNormEssSup (f := f) (μ := μ d))
    _ = _ := by simp

theorem infinityStrongBound : MaximalStrongSpec.InfinityStrongBound := by
  intro d _ 𝕜 _ _ _ b f hf
  change MemLp f ∞ (μ d) at hf
  have hb : ∀ x, maximalValue b f x ≤ eLpNorm f ∞ (μ d) := by
    intro x
    cases b
    · change centered f x ≤ _
      exact iSup_le fun r => iSup_le fun hr => ballAverage_le_infinity f hf r hr x
    · change uncentered f x ≤ _
      exact iSup_le fun z => iSup_le fun r => iSup_le fun hr => iSup_le fun _ =>
        ballAverage_le_infinity f hf r hr z
  exact ⟨hb, essSup_le_of_ae_le _ (Eventually.of_forall hb)⟩

lemma maximal_le_double_centered (b : Bool) (f : Point d → 𝕜)
    (hf : locallyIntegrable f) (x : Point d) :
    maximalValue b f x ≤ (2 : ℝ≥0∞)^d * centered f x := by
  cases b
  · exact (centered_le_uncentered f x).trans (uncentered_le_centered f hf x)
  · exact uncentered_le_centered f hf x

/-- Consequences of a finite extended moment; toReal is used only after the
actual extended maximal function is proved finite a.e. -/
lemma membership_of_moment (u : Point d → ℝ≥0∞) (hm : Measurable u)
    (p : ℝ) (hp : 0 < p) (B : ℝ≥0∞) (hB : B < ∞)
    (hb : (∫⁻ x, u x ^ p ∂(μ d)) ^ (1 / p) ≤ B) :
    (∀ᵐ x ∂(μ d), u x < ∞) ∧
      MemLp (fun x => (u x).toReal) (ENNReal.ofReal p) (μ d) ∧
      eLpNorm (fun x => (u x).toReal) (ENNReal.ofReal p) (μ d) ≤ B := by
  have hbound := hb.trans_lt hB
  have hint : (∫⁻ x, u x ^ p ∂(μ d)) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr hp)).mp hbound
  have hfinite : ∀ᵐ x ∂(μ d), u x < ∞ := by
    filter_upwards [ae_lt_top (hm.pow_const p) hint.ne] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hp).mp hx
  have hg : AEStronglyMeasurable (fun x => (u x).toReal) (μ d) :=
    hm.ennreal_toReal.aestronglyMeasurable
  have heq : eLpNorm (fun x => (u x).toReal) (ENNReal.ofReal p) (μ d) =
      (∫⁻ x, u x ^ p ∂(μ d)) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hg,
      ENNReal.toReal_ofReal hp.le]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hfinite] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hx.ne]
  exact ⟨hfinite, heq.trans_lt hbound, heq.trans_le hb⟩

theorem finiteStrongBound : MaximalStrongSpec.FiniteStrongBound := by
  intro d _ p hp
  obtain ⟨C, hC⟩ := centered_finite_bound (d := d) p hp
  refine ⟨(2 : ℝ≥0)^d * C, ?_⟩
  intro 𝕜 _ _ _ b f hf
  change MemLp f (ENNReal.ofReal p) (μ d) at hf
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hfl : locallyIntegrable f := localIntegrability _ hp1 f hf
  have hm := (sublinear b f hfl).1
  have hcm := (MaximalWeak.measurable_maximal f hfl).1
  change Measurable (centered f) at hcm
  have hb : (∫⁻ x, maximalValue b f x ^ p ∂(μ d)) ^ (1 / p) ≤
      (((2 : ℝ≥0)^d * C : ℝ≥0) : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (μ d) := by
    calc
      _ ≤ (∫⁻ x, ((2 : ℝ≥0∞)^d * centered f x) ^ p ∂(μ d)) ^ (1 / p) := by
        apply ENNReal.rpow_le_rpow _ (by positivity)
        exact lintegral_mono fun x => ENNReal.rpow_le_rpow
          (maximal_le_double_centered b f hfl x) hp0.le
      _ = (2 : ℝ≥0∞)^d * (∫⁻ x, centered f x ^ p ∂(μ d)) ^ (1 / p) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rw [lintegral_const_mul _ (hcm.pow_const p),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
      _ ≤ (2 : ℝ≥0∞)^d * ((C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (μ d)) :=
        mul_le_mul_of_nonneg_left (hC f hf) (by positivity)
      _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, mul_assoc]
  refine ⟨hb, ?_⟩
  exact membership_of_moment _ hm p hp0 _
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hf) hb
end Completed
end P102.U2.MaximalStrong
