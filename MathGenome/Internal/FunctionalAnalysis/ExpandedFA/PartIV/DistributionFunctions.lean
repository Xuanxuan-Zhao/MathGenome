import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.DistributionFunctions

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV

/-- The distribution of the modulus, with strict superlevel sets. -/
noncomputable def distribution {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E) (t : ℝ) : ℝ≥0∞ := μ {x | t < ‖f x‖}

/-- The primitive is a nonnegative Lebesgue integral; infinite values are retained. -/
noncomputable def layerPrimitive (h : ℝ → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo 0 s, h t

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

theorem distribution_antitone :
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) (f : Ω → E), Antitone (distribution μ f) := by
  intro Ω E _ _ μ f s t hst
  exact measure_mono (fun x hx => lt_of_le_of_lt hst hx)

theorem distribution_rightContinuous :
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E),
    Measurable (fun x => ‖f x‖) → ∀ t : ℝ,
      ContinuousWithinAt (distribution μ f) (Ici t) t := by
  intro Ω E _ _ μ _ f hf t
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝[≥] t)
    (measurableSet_lt measurable_const hf) (fun s => measurableSet_lt measurable_const hf)
  apply ae_of_all
  intro x
  by_cases hx : t < ‖f x‖
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with s hs
    simpa [hx] using hs
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [hx, iff_false, not_lt]
    exact (le_of_not_gt hx).trans hs

theorem distribution_leftLimit :
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E),
    Measurable (fun x => ‖f x‖) → ∀ t : ℝ,
      Function.leftLim (distribution μ f) t = μ {x | t ≤ ‖f x‖} := by
  intro Ω E _ _ μ _ f hf t
  apply tendsto_nhds_unique ((distribution_antitone μ f).tendsto_leftLim t)
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝[<] t)
    (measurableSet_le measurable_const hf) (fun s => measurableSet_lt measurable_const hf)
  apply ae_of_all
  intro x
  by_cases hx : t ≤ ‖f x‖
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simpa [hx] using lt_of_lt_of_le hs hx
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (lt_of_not_ge hx))] with s hs
    simp only [hx, iff_false, not_lt]
    exact hs.le

theorem distribution_countableJumps :
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) (f : Ω → E),
    {t : ℝ | ¬ ContinuousAt (distribution μ f) t}.Countable ∧
    {t : ℝ | μ {x | t ≤ ‖f x‖} ≠ distribution μ f t}.Countable := by
  intro Ω E _ _ μ f
  exact ⟨(distribution_antitone μ f).countable_not_continuousAt,
    countable_meas_le_ne_meas_lt μ (fun x => ‖f x‖)⟩

theorem distribution_limitBounds :
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (fs : ℕ → Ω → E),
    Measurable (fun x => ‖f x‖) → (∀ n, Measurable (fun x => ‖fs n x‖)) →
    (∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) →
    ∀ t : ℝ, 0 < t →
      distribution μ f t ≤ liminf (fun n => distribution μ (fs n) t) atTop ∧
      liminf (fun n => distribution μ (fs n) t) atTop ≤
        limsup (fun n => distribution μ (fs n) t) atTop ∧
      limsup (fun n => distribution μ (fs n) t) atTop ≤
        Function.leftLim (distribution μ f) t := by
  intro Ω E _ _ μ _ f fs hf hfs hconv t _ht
  let A : ℕ → Set Ω := fun n => {x | t < ‖fs n x‖}
  let B : Set Ω := {x | t < ‖f x‖}
  let C : Set Ω := {x | t ≤ ‖f x‖}
  let F : ℕ → Ω → ℝ≥0∞ := fun n => (A n).indicator (fun _ => 1)
  have hA : ∀ n, MeasurableSet (A n) := fun n => measurableSet_lt measurable_const (hfs n)
  have hB : MeasurableSet B := measurableSet_lt measurable_const hf
  have hC : MeasurableSet C := measurableSet_le measurable_const hf
  have hF : ∀ n, Measurable (F n) := fun n => measurable_const.indicator (hA n)
  have hlo : μ B ≤ liminf (fun n => μ (A n)) atTop := by
    simp_rw [← lintegral_indicator_one hB, ← lintegral_indicator_one (hA _)]
    refine (lintegral_mono_ae ?_).trans (lintegral_liminf_le hF)
    filter_upwards [hconv] with x hx
    by_cases hxt : t < ‖f x‖
    · rw [indicator_of_mem (show x ∈ B from hxt)]
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [(tendsto_order.1 hx.norm).1 t hxt] with n hn
      simp [A, hn]
    · simp [B, hxt]
  have hhi : limsup (fun n => μ (A n)) atTop ≤ μ C := by
    simp_rw [← lintegral_indicator_one hC, ← lintegral_indicator_one (hA _)]
    refine (limsup_lintegral_le (fun _ => 1) hF
      (fun n => ae_of_all _ (fun x => indicator_le_self' (fun _ _ => zero_le_one) x))
      (by simp)).trans (lintegral_mono_ae ?_)
    filter_upwards [hconv] with x hx
    by_cases hxt : t ≤ ‖f x‖
    · rw [indicator_of_mem (show x ∈ C from hxt)]
      refine limsup_le_of_le (by isBoundedDefault) ?_
      exact Eventually.of_forall fun n => indicator_le_self' (fun _ _ => zero_le_one) x
    · rw [indicator_of_notMem (show x ∉ C from hxt)]
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [(tendsto_order.1 hx.norm).2 t (lt_of_not_ge hxt)] with n hn
      simp [F, A, hn.not_gt]
  exact ⟨hlo, liminf_le_limsup, by rwa [distribution_leftLimit μ f hf t]⟩

theorem distribution_levelConvergence :
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (fs : ℕ → Ω → E),
    Measurable (fun x => ‖f x‖) → (∀ n, Measurable (fun x => ‖fs n x‖)) →
    (∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) →
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n => distribution μ (fs n) t) atTop (𝓝 (distribution μ f t)) := by
  intro Ω E _ _ μ _ f fs hf hfs hconv
  have heq := meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi (0 : ℝ))) (fun x => ‖f x‖)
  filter_upwards [heq, self_mem_ae_restrict measurableSet_Ioi] with t ht hpos
  have hb := distribution_limitBounds μ f fs hf hfs hconv t hpos
  apply tendsto_of_le_liminf_of_limsup_le hb.1
  simpa [distribution_leftLimit μ f hf t, distribution, ht] using hb.2.2

theorem distribution_layerCake :
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E),
    Measurable (fun x => ‖f x‖) → ∀ h : ℝ → ℝ≥0∞, Measurable h →
      (∫⁻ x, layerPrimitive h ‖f x‖ ∂μ) =
        ∫⁻ t in Ioi 0, distribution μ f t * h t := by
  intro Ω E _ _ μ _ f hf h hh
  let F : Ω → ℝ → ℝ≥0∞ := fun x => (Ioo 0 ‖f x‖).indicator h
  have hm : Measurable (Function.uncurry F) := by
    exact (hh.comp measurable_snd).indicator
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (hf.comp measurable_fst)))
  change (∫⁻ x, ∫⁻ t in Ioo 0 ‖f x‖, h t ∂volume ∂μ) = _
  simp_rw [← lintegral_indicator measurableSet_Ioo]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro t
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have he : (fun x => F x t) = {x | t < ‖f x‖}.indicator (fun _ => h t) := by
      funext x
      simp [F, indicator_apply, ht]
    change (∫⁻ x, F x t ∂μ) = _
    rw [he, lintegral_indicator (measurableSet_lt measurable_const hf), setLIntegral_const]
    exact mul_comm _ _
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    have he : (fun x => F x t) = 0 := by
      funext x
      simp [F, ht]
    change (∫⁻ x, F x t ∂μ) = _
    rw [he]
    exact lintegral_zero_fun

theorem distribution_tail :
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E),
    Measurable (fun x => ‖f x‖) → ∀ h : ℝ → ℝ≥0∞, Measurable h →
    ∀ a : ℝ, 0 ≤ a →
      (∫⁻ x in {x | a < ‖f x‖}, layerPrimitive h ‖f x‖ ∂μ) =
        distribution μ f a * layerPrimitive h a +
          ∫⁻ t in Ioi a, distribution μ f t * h t := by
  intro Ω E _ _ μ _ f hf h hh a ha
  rw [distribution_layerCake (μ.restrict {x | a < ‖f x‖}) f hf h hh]
  have hunion : Ioc 0 a ∪ Ioi a = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact lt_of_le_of_lt ha ht
    · intro ht
      exact (le_or_gt t a).elim (fun hta => Or.inl ⟨ht, hta⟩) Or.inr
  rw [← hunion, lintegral_union measurableSet_Ioi (by
    apply disjoint_left.2
    intro t ht hs
    exact (not_lt_of_ge ht.2) hs)]
  congr 1
  · calc
      _ = ∫⁻ t in Ioc 0 a, distribution μ f a * h t := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        dsimp only
        congr 1
        unfold distribution
        rw [Measure.restrict_apply (measurableSet_lt measurable_const hf)]
        congr 1
        ext x
        exact and_iff_right_of_imp (fun hx => lt_of_le_of_lt ht.2 hx)
      _ = distribution μ f a * layerPrimitive h a := by
        rw [lintegral_const_mul _ hh]
        unfold layerPrimitive
        rw [restrict_Ioo_eq_restrict_Ioc]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    congr 1
    unfold distribution
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hf)]
    congr 1
    ext x
    exact and_iff_left_of_imp (fun hx => (show a < ‖f x‖ from lt_trans ht hx))

theorem distribution_tendsto_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → E) (hf : Measurable (fun x => ‖f x‖)) :
    Tendsto (distribution μ f) atTop (𝓝 0) := by
  have hi : (⋂ t : ℝ, {x | t < ‖f x‖}) = (∅ : Set Ω) := by
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    have h := mem_iInter.1 hx (‖f x‖)
    exact (lt_irrefl _) (show ‖f x‖ < ‖f x‖ from h)
  have hh := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun t : ℝ => {x | t < ‖f x‖})
    (fun _ => (measurableSet_lt measurable_const hf).nullMeasurableSet)
    (fun s t hst x hx => lt_of_le_of_lt hst hx) ⟨0, measure_ne_top _ _⟩
  rw [hi, measure_empty] at hh
  exact hh

theorem distribution_powerDecay_of_lintegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → E) (hf : Measurable (fun x => ‖f x‖)) (q : ℝ) (hq : 0 < q)
    (hfin : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q) ∂μ) ≠ ∞) :
    Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ q) * distribution μ f t) atTop (𝓝 0) := by
  have htail := tendsto_setLIntegral_zero hfin (distribution_tendsto_zero μ f hf)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [distribution, ← setLIntegral_const]
  apply setLIntegral_mono' (measurableSet_lt measurable_const hf)
  intro x hx
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ht hx.le hq.le)

theorem distribution_powerDecay :
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E],
  ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (q : ℝ), 0 < q →
    MemLp f (ENNReal.ofReal q) μ →
      Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ q) * distribution μ f t)
        atTop (𝓝 0) := by
  intro Ω E _ _ μ _ f q hq hmem
  let g : Ω → ℝ := hmem.aestronglyMeasurable.norm.mk (fun x => ‖f x‖)
  have hg : Measurable g := hmem.aestronglyMeasurable.norm.measurable_mk
  have hge : (fun x => ‖g x‖) =ᵐ[μ] (fun x => ‖f x‖) := by
    filter_upwards [hmem.aestronglyMeasurable.norm.ae_eq_mk] with x hx
    dsimp [g]
    rw [← hx]
    exact abs_of_nonneg (norm_nonneg _)
  have hd : distribution μ g = distribution μ f := by
    funext t
    apply measure_congr
    filter_upwards [hge] with x hx using by simp [hx]
  have hi : (∫⁻ x, ‖f x‖ₑ ^ q ∂μ) < ∞ := by
    have hp := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top hmem
    simpa [ENNReal.toReal_ofReal hq.le] using hp
  have hfin : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q) ∂μ) ≠ ∞ := by
    have he : (fun x => ENNReal.ofReal (‖g x‖ ^ q)) =ᵐ[μ]
        (fun x => ‖f x‖ₑ ^ q) := by
      filter_upwards [hge] with x hx
      rw [hx, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le, ofReal_norm]
    rw [lintegral_congr_ae he]
    exact hi.ne
  simpa [hd] using distribution_powerDecay_of_lintegral μ g hg.norm q hq hfin

end ExpandedFA.PartIV
