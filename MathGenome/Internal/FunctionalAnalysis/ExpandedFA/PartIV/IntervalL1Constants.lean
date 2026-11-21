import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.IntervalL1Constants
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTraceAndKernel
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
open ExpandedFA.Sobolev.OneDimensional

namespace ExpandedFA.PartIV.IntervalL1

variable {𝕜 : Type} [RCLike 𝕜]

theorem representative_continuous {u : W11 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) : ContinuousOn f (Icc (0 : ℝ) 1) := by
  have hc : closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  exact hc ▸ hf.1

theorem supNorm_le {f : ℝ → 𝕜} {C : ℝ}
    (h : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C) : supNorm f ≤ C := by
  apply csSup_le
  · exact ⟨‖f 0‖, ⟨0, by norm_num, rfl⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx

theorem norm_le_supNorm {f : ℝ → 𝕜} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖f x‖ ≤ supNorm f := by
  apply le_csSup (isCompact_Icc.bddAbove_image hf.norm)
  exact ⟨x, hx, rfl⟩

theorem supNorm_nonneg {f : ℝ → 𝕜} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    0 ≤ supNorm f :=
  (norm_nonneg (f 0)).trans (norm_le_supNorm hf (by norm_num))

/-- A continuous a.e. upper bound on the open interval extends to both
endpoints. The min formulation uses the accepted open-set a.e. equality lemma. -/
theorem continuous_norm_bound_of_ae {f : ℝ → 𝕜} {C : ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (ha : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), ‖f x‖ ≤ C) :
    ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C := by
  have he : (fun x => min ‖f x‖ C) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun x => ‖f x‖) := ha.mono (fun _ h => min_eq_left h)
  have hm := Measure.eqOn_Ioo_of_ae_eq volume he
    ((hf.norm.inf continuousOn_const).mono Ioo_subset_Icc_self)
    (hf.norm.mono Ioo_subset_Icc_self)
  have hb : ∀ x ∈ Ioo (0 : ℝ) 1, ‖f x‖ ≤ C := by
    intro x hx
    exact min_eq_left_iff.mp (hm hx)
  intro x hx
  have hc : closure (Ioo (0 : ℝ) 1) = Icc (0 : ℝ) 1 := closure_Ioo (by norm_num)
  exact le_on_closure hb (hc.symm ▸ hf.norm) continuousOn_const (hc.symm ▸ hx)

theorem supNorm_eq_essentialSup {f : ℝ → 𝕜}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    eLpNorm f ∞ (volume.restrict (Ioo (0 : ℝ) 1)) = ENNReal.ofReal (supNorm f) := by
  have hu : eLpNormEssSup f (volume.restrict (Ioo (0 : ℝ) 1)) ≤
      ENNReal.ofReal (supNorm f) := by
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact norm_le_supNorm hf (Ioo_subset_Icc_self hx)
  have hn : eLpNormEssSup f (volume.restrict (Ioo (0 : ℝ) 1)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have ha : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      ‖f x‖ ≤ (eLpNormEssSup f (volume.restrict (Ioo (0 : ℝ) 1))).toReal := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f
      (volume.restrict (Ioo (0 : ℝ) 1))] with x hx
    exact (ENNReal.ofReal_le_iff_le_toReal hn).mp (by simpa using hx)
  rw [eLpNorm_exponent_top ((hf.mono Ioo_subset_Icc_self).aestronglyMeasurable
    measurableSet_Ioo)]
  apply le_antisymm hu
  exact (ENNReal.ofReal_le_iff_le_toReal hn).mpr
    (supNorm_le (continuous_norm_bound_of_ae hf ha))

theorem sup_norm_identification :
    Specs.ExpandedFA.PartIV.IntervalL1Constants.SupNormIdentification := by
  intro 𝕜 _ u f hf
  exact supNorm_eq_essentialSup (representative_continuous hf)

theorem primitive_oscillation_bound {u : W11 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖f x - f y‖ ≤ ‖derivativeLp u‖ := by
  have hc : closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  simpa [reciprocalExponent] using primitive_increment_bound_closure
    ordConnected_Ioo u hf (hc ▸ hx) (hc ▸ hy)

theorem derivative_norm_pos {u : W11 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) (hn : Nonconstant f) :
    0 < ‖derivativeLp u‖ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  exact (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)).trans_le
    (primitive_oscillation_bound hf hx hy)

theorem mean_difference_integral {u : W11 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) (x : ℝ) :
    f x - mean f = ∫ y in (0 : ℝ)..1, f x - f y := by
  rw [intervalIntegral.integral_sub (intervalIntegrable_const)
    ((representative_continuous hf).intervalIntegrable_of_Icc (by norm_num)),
    intervalIntegral.integral_const]
  simp [mean]

theorem mean_sup_bound : Specs.ExpandedFA.PartIV.IntervalL1Constants.MeanSupBound := by
  intro 𝕜 _ u f hf
  apply supNorm_le
  intro x hx
  rw [mean_difference_integral hf]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ‖derivativeLp u‖)
    (fun y hy => primitive_oscillation_bound hf hx (by
      exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy)))

/-- Strictness follows without an integral-kernel formula: at y=x the
continuous oscillation integrand is zero, while the variation is positive. -/
theorem mean_sup_strict : Specs.ExpandedFA.PartIV.IntervalL1Constants.MeanSupStrict := by
  intro 𝕜 _ u f hf hn
  have hfc := representative_continuous hf
  have hd := derivative_norm_pos hf hn
  apply (isCompact_Icc.sSup_lt_iff_of_continuous (by exact ⟨0, by norm_num⟩)
    (hfc.sub continuousOn_const).norm _).mpr
  intro x hx
  change ‖f x - mean f‖ < _
  rw [mean_difference_integral hf]
  have hosc : ContinuousOn (fun y => ‖f x - f y‖) (Icc (0 : ℝ) 1) :=
    (continuousOn_const.sub hfc).norm
  have hs := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1) hosc continuousOn_const
    (fun y hy => primitive_oscillation_bound hf hx (Ioc_subset_Icc_self hy))
    (show ∃ y ∈ Icc (0 : ℝ) 1, ‖f x - f y‖ < ‖derivativeLp u‖ from
      ⟨x, hx, by simpa using hd⟩)
  have hb := intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun y => f x - f y) (μ := volume)
  exact hb.trans_lt (by simpa using hs)

/-- The real-coordinate integral of the actual weak derivative has exactly
its accepted Lp norm. Endpoint null sets contribute no mass. -/
theorem derivative_l1Norm (u : W11 𝕜) :
    l1Norm (lineFunction (derivativeLp u)) = ‖derivativeLp u‖ := by
  rw [l1Norm, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  have hm := lineFunction_memLp (derivativeLp u)
  change (∫ t, ‖lineFunction (derivativeLp u) t‖ ∂volume.restrict (unitInterval : Set ℝ)) = _
  rw [← lineFunction_norm (derivativeLp u),
    eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable,
    integral_norm_eq_lintegral_enorm hm.aestronglyMeasurable]

/-- At zero trace both endpoint primitive formulas constrain the same value. -/
theorem zero_endpoint_pointwise_bound {u : W11 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) (h0 : f 0 = 0) (h1 : f 1 = 0)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖f x‖ ≤ (1 / 2 : ℝ) * ‖derivativeLp u‖ := by
  have hc : closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hcx : x ∈ closure (unitInterval : Set ℝ) := hc ▸ hx
  have hc0 : (0 : ℝ) ∈ closure (unitInterval : Set ℝ) := by rw [hc]; norm_num
  have hc1 : (1 : ℝ) ∈ closure (unitInterval : Set ℝ) := by rw [hc]; norm_num
  have hleft := hf.2.2.2 x hcx 0 hc0
  have hright := hf.2.2.2 1 hc1 x hcx
  have hl : ‖f x‖ ≤ ∫ t in (0 : ℝ)..x, ‖lineFunction (derivativeLp u) t‖ := by
    rw [h0, sub_zero] at hleft
    rw [hleft.2]
    exact intervalIntegral.norm_integral_le_integral_norm hx.1
  have hr : ‖f x‖ ≤ ∫ t in x..(1 : ℝ), ‖lineFunction (derivativeLp u) t‖ := by
    rw [h1, zero_sub] at hright
    calc
      ‖f x‖ = ‖∫ t in x..(1 : ℝ), lineFunction (derivativeLp u) t‖ := by
        rw [← hright.2, norm_neg]
      _ ≤ _ := intervalIntegral.norm_integral_le_integral_norm hx.2
  have hi := intervalIntegral.integral_add_adjacent_intervals hleft.1.norm hright.1.norm
  rw [← l1Norm, derivative_l1Norm] at hi
  linarith

theorem zero_sup_bound : Specs.ExpandedFA.PartIV.IntervalL1Constants.ZeroSupBound := by
  intro 𝕜 _ u f hf hu
  obtain ⟨h0, h1⟩ := ExpandedFA.Sobolev.Trace.interval_zeroSpace_endpoints
    𝕜 0 1 (by norm_num) 1 (by norm_num) u hu f hf
  exact supNorm_le (fun _ hx => zero_endpoint_pointwise_bound hf h0 h1 hx)

/-- The specified weak derivative is the classical derivative of this very
representative a.e.; no derivative regularity is added as a hypothesis. -/
theorem primitive_ae_hasDerivAt {u : W11 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt f (lineFunction (derivativeLp u) t) t := by
  have hc : closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hc0 : (0 : ℝ) ∈ closure (unitInterval : Set ℝ) := by rw [hc]; norm_num
  have he : ∀ y ∈ Ioo (0 : ℝ) 1,
      f y = canonicalPrimitive (derivativeLp u) y + f 0 := by
    intro y hy
    have hp := canonicalPrimitive_sub_eq ordConnected_Ioo (derivativeLp u)
      (subset_closure hy) hc0
    have hz : canonicalPrimitive (derivativeLp u) 0 = 0 := by simp [canonicalPrimitive]
    rw [hz, sub_zero] at hp
    have hf' := (hf.2.2.2 y (subset_closure hy) 0 hc0).2
    rw [← hp] at hf'
    exact sub_eq_iff_eq_add.mp hf'
  have hd := canonicalPrimitive_ae_hasDerivAt (derivativeLp u)
  change ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), _ at hd
  filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t ht hti
  apply (ht.add_const (f 0)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hti] with y hy
  exact he y hy

/-- For a real monotone part of an AC representative, variation is exactly
its rise. Endpoints a=b are retained. -/
theorem monotone_derivative_norm_integral {u : W11 ℝ} {f : ℝ → ℝ}
    (hf : PrimitiveRepresentative u f) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hm : MonotoneOn f (Icc a b)) :
    (∫ t in a..b, ‖lineFunction (derivativeLp u) t‖) = f b - f a := by
  have hc : closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hac : a ∈ closure (unitInterval : Set ℝ) := by rw [hc]; exact ⟨ha, hab.trans hb⟩
  have hbc : b ∈ closure (unitInterval : Set ℝ) := by rw [hc]; exact ⟨ha.trans hab, hb⟩
  have hd := ae_restrict_of_ae_restrict_of_subset
    (show Ioo a b ⊆ Ioo (0 : ℝ) 1 from fun _ ht => ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩)
    (primitive_ae_hasDerivAt hf)
  have he : (fun t => ‖lineFunction (derivativeLp u) t‖)
      =ᵐ[volume.restrict (Ioo a b)] lineFunction (derivativeLp u) := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t hdt ht
    have hs := hm.derivWithin_nonneg (x := t)
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hdt.deriv] at hs
    exact Real.norm_of_nonneg hs
  calc
    _ = ∫ t in a..b, lineFunction (derivativeLp u) t := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      exact integral_congr_ae he
    _ = _ := (hf.2.2.2 b hbc a hac).2.symm

/-- The descending side has variation equal to its fall. -/
theorem antitone_derivative_norm_integral {u : W11 ℝ} {f : ℝ → ℝ}
    (hf : PrimitiveRepresentative u f) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hm : AntitoneOn f (Icc a b)) :
    (∫ t in a..b, ‖lineFunction (derivativeLp u) t‖) = f a - f b := by
  have hc : closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hac : a ∈ closure (unitInterval : Set ℝ) := by rw [hc]; exact ⟨ha, hab.trans hb⟩
  have hbc : b ∈ closure (unitInterval : Set ℝ) := by rw [hc]; exact ⟨ha.trans hab, hb⟩
  have hd := ae_restrict_of_ae_restrict_of_subset
    (show Ioo a b ⊆ Ioo (0 : ℝ) 1 from fun _ ht => ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩)
    (primitive_ae_hasDerivAt hf)
  have he : (fun t => ‖lineFunction (derivativeLp u) t‖)
      =ᵐ[volume.restrict (Ioo a b)] (fun t => -lineFunction (derivativeLp u) t) := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t hdt ht
    have hs := hm.derivWithin_nonpos (x := t)
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hdt.deriv] at hs
    exact Real.norm_of_nonpos hs
  calc
    _ = ∫ t in a..b, -lineFunction (derivativeLp u) t := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      exact integral_congr_ae he
    _ = _ := by rw [intervalIntegral.integral_neg, ← (hf.2.2.2 b hbc a hac).2]; ring

/-- Every nonzero nonnegative unimodal AC tent is an optimizer. The argument
allows flat tops and nonlinear monotone sides. -/
theorem tent_equality : Specs.ExpandedFA.PartIV.IntervalL1Constants.TentEquality := by
  intro u f hf ht
  obtain ⟨h0, h1, hn, ⟨x, hx, hxn⟩, c, hc, hm, ha⟩ := ht
  have hcx : f x ≤ f c := by
    rcases le_total x c with h | h
    · exact hm ⟨hx.1, h⟩ ⟨hc.1, le_rfl⟩ h
    · exact ha ⟨le_rfl, hc.2⟩ ⟨h, hx.2⟩ h
  have hcp : 0 < f c := (lt_of_le_of_ne (hn x hx) (Ne.symm hxn)).trans_le hcx
  have hs : supNorm f = f c := by
    apply le_antisymm
    · apply supNorm_le
      intro y hy
      rw [Real.norm_of_nonneg (hn y hy)]
      rcases le_total y c with h | h
      · exact hm ⟨hy.1, h⟩ ⟨hc.1, le_rfl⟩ h
      · exact ha ⟨le_rfl, hc.2⟩ ⟨h, hy.2⟩ h
    · simpa [Real.norm_of_nonneg (hn c hc)] using
        norm_le_supNorm (representative_continuous hf) hc
  have hcl : closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hc0 : (0 : ℝ) ∈ closure (unitInterval : Set ℝ) := by rw [hcl]; norm_num
  have hc1 : (1 : ℝ) ∈ closure (unitInterval : Set ℝ) := by rw [hcl]; norm_num
  have hcc : c ∈ closure (unitInterval : Set ℝ) := hcl.symm ▸ hc
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hf.2.2.2 c hcc 0 hc0).1.norm (hf.2.2.2 1 hc1 c hcc).1.norm
  rw [monotone_derivative_norm_integral hf (by norm_num) hc.2 hc.1 hm,
    antitone_derivative_norm_integral hf hc.1 (by norm_num) hc.2 ha,
    ← l1Norm, derivative_l1Norm, h0, h1] at hi
  refine ⟨?_, ?_, ?_⟩
  · exact ExpandedFA.Sobolev.Trace.interval_zeroSpace_of_endpoints
      (by norm_num) (by norm_num) u f hf h0 h1
  · linarith
  · rw [hs]; linarith


/-- Lebesgue measure on the closed unit interval, used for Fubini. Endpoints
are null, so its integrals are the usual interval integrals. -/
abbrev intervalMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

theorem integral_intervalMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (h : ℝ → E) :
    (∫ x, h x ∂intervalMeasure) = ∫ x in (0 : ℝ)..1, h x := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_Icc_eq_integral_Ioc

/-- The primitive kernel before subtracting its mean. -/
def stepKernel (x t : ℝ) : ℝ := if t ≤ x then 1 else 0

/-- The mean-zero primitive kernel. -/
def meanKernel (x t : ℝ) : ℝ := stepKernel x t - (1 - t)

theorem measurable_stepKernel : Measurable (Function.uncurry stepKernel) := by
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    measurable_const measurable_const

theorem measurable_meanKernel : Measurable (Function.uncurry meanKernel) :=
  measurable_stepKernel.sub (measurable_const.sub measurable_snd)

theorem stepKernel_bound (x t : ℝ) : |stepKernel x t| ≤ 1 := by
  unfold stepKernel
  split_ifs <;> norm_num

theorem meanKernel_bound (x : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |meanKernel x t| ≤ 1 := by
  unfold meanKernel stepKernel
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [ht.1, ht.2]

theorem kernel_smul_integrable {g : ℝ → 𝕜} (hg : Integrable g intervalMeasure)
    {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k))
    (hkb : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1, |k x t| ≤ 1) :
    Integrable (fun z : ℝ × ℝ => k z.1 z.2 • g z.2)
      (intervalMeasure.prod intervalMeasure) := by
  apply (hg.norm.comp_snd intervalMeasure).mono'
    (hk.aestronglyMeasurable.smul hg.aestronglyMeasurable.comp_snd)
  have ht : ∀ᵐ z ∂intervalMeasure.prod intervalMeasure, z.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc))
  filter_upwards [ht] with z hz
  change ‖k z.1 z.2 • g z.2‖ ≤ ‖g z.2‖
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hkb _ _ hz)

theorem kernel_smul_integrable_section {g : ℝ → 𝕜}
    (hg : Integrable g intervalMeasure) {k : ℝ → ℝ → ℝ}
    (hk : Measurable (Function.uncurry k))
    (hkb : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1, |k x t| ≤ 1) (x : ℝ) :
    Integrable (fun t => k x t • g t) intervalMeasure := by
  apply hg.norm.mono' ((hk.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.smul
    hg.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change ‖k x t • g t‖ ≤ ‖g t‖
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hkb _ _ ht)

theorem integral_stepKernel_smul (g : ℝ → 𝕜) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ t, stepKernel x t • g t ∂intervalMeasure) = ∫ t in (0 : ℝ)..x, g t := by
  rw [integral_intervalMeasure]
  have he : (fun t => stepKernel x t • g t) = (Iic x).indicator g := by
    ext t
    simp [stepKernel, indicator]
  rw [he]
  exact intervalIntegral.integral_indicator (f := g) hx

theorem integral_stepKernel {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, stepKernel x t ∂intervalMeasure) = 1 - t := by
  change (∫ x in Icc (0 : ℝ) 1, (Ici t).indicator (fun _ => (1 : ℝ)) x) = _
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  rw [show Ici t ∩ Icc (0 : ℝ) 1 = Icc t 1 by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h, _, h1⟩; exact ⟨h, h1⟩
    · rintro ⟨h, h1⟩; exact ⟨h, ht.1.trans h, h1⟩]
  simp [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2)]

theorem integral_abs_meanKernel {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, |meanKernel x t| ∂intervalMeasure) = 2 * t * (1 - t) := by
  have he : (fun x => |meanKernel x t|) =
      (fun x => (1 - t) + (2 * t - 1) * stepKernel x t) := by
    ext x
    unfold meanKernel stepKernel
    split_ifs
    · rw [show (1 : ℝ) - (1 - t) = t by ring, abs_of_nonneg ht.1]
      ring
    · rw [show (0 : ℝ) - (1 - t) = -(1 - t) by ring,
        abs_neg, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      ring
  rw [he, integral_add (integrable_const _) ?_, integral_const, integral_const_mul,
    integral_stepKernel ht]
  · norm_num [measureReal_def, Real.volume_Icc]
    ring
  · exact ((integrable_const (1 : ℝ)).mono'
      (measurable_stepKernel.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa using stepKernel_bound x t))).const_mul _


theorem derivative_integrable (u : W11 𝕜) :
    Integrable (lineFunction (derivativeLp u)) intervalMeasure := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
  exact lineFunction_intervalIntegrable_closure ordConnected_Ioo (derivativeLp u)
    (by rw [show closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 from
      closure_Ioo (by norm_num)]; norm_num)
    (by rw [show closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 from
      closure_Ioo (by norm_num)]; norm_num)

/-- Fubini identifies the mean of the primitive with its linear moment. -/
theorem mean_primitive_formula {u : W11 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) :
    mean f = f 0 + ∫ t, (1 - t) • lineFunction (derivativeLp u) t ∂intervalMeasure := by
  let g := lineFunction (derivativeLp u)
  have hg := derivative_integrable u
  have hc : closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 := closure_Ioo (by norm_num)
  have hp (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      f x = f 0 + ∫ t, stepKernel x t • g t ∂intervalMeasure := by
    rw [integral_stepKernel_smul g hx, ← (hf.2.2.2 x (hc.symm ▸ hx) 0
      (by rw [hc]; norm_num)).2]
    abel
  have hi := kernel_smul_integrable hg measurable_stepKernel
    (fun x t _ => stepKernel_bound x t)
  have hs := integral_integral_swap (f := fun x t => stepKernel x t • g t) hi
  change (∫ x, ∫ t, stepKernel x t • g t ∂intervalMeasure ∂intervalMeasure) = _ at hs
  have hr : (∫ t, ∫ x, stepKernel x t • g t ∂intervalMeasure ∂intervalMeasure) =
      ∫ t, (1 - t) • g t ∂intervalMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [integral_smul_const, integral_stepKernel ht]
  unfold mean
  rw [← integral_intervalMeasure]
  calc
    (∫ x, f x ∂intervalMeasure) =
        ∫ x, f 0 + ∫ t, stepKernel x t • g t ∂intervalMeasure ∂intervalMeasure := by
      apply setIntegral_congr_fun measurableSet_Icc
      exact hp
    _ = f 0 + ∫ x, ∫ t, stepKernel x t • g t ∂intervalMeasure ∂intervalMeasure := by
      rw [integral_add (integrable_const _) hi.integral_prod_left, integral_const]
      norm_num [measureReal_def, Real.volume_Icc]
      rfl
    _ = _ := by rw [hs, hr]

/-- Exact kernel representation of the original AC representative. -/
theorem mean_kernel_formula {u : W11 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    f x - mean f =
      ∫ t, meanKernel x t • lineFunction (derivativeLp u) t ∂intervalMeasure := by
  have hg := derivative_integrable u
  have hi := kernel_smul_integrable_section hg measurable_stepKernel
    (fun x t _ => stepKernel_bound x t) x
  have hj : Integrable (fun t => (1 - t) • lineFunction (derivativeLp u) t)
      intervalMeasure := by
    apply hg.bdd_smul 1 (measurable_const.sub measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change |1 - t| ≤ 1
    rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
    linarith [ht.1]
  simp only [meanKernel]
  simp_rw [sub_smul (stepKernel x _) (1 - _) (_ : 𝕜)]
  rw [integral_sub hi hj, integral_stepKernel_smul _ hx, mean_primitive_formula hf]
  have hc : closure (unitInterval : Set ℝ) = Icc (0 : ℝ) 1 := closure_Ioo (by norm_num)
  rw [← (hf.2.2.2 x (hc.symm ▸ hx) 0 (by rw [hc]; norm_num)).2]
  abel

/-- The quantitative weighted estimate retains the strict deficit except at
one null midpoint. -/
theorem mean_l1_weighted_bound {u : W11 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) :
    l1Norm (fun x => f x - mean f) ≤
      ∫ t, (2 * t * (1 - t)) * ‖lineFunction (derivativeLp u) t‖ ∂intervalMeasure := by
  let g := lineFunction (derivativeLp u)
  have hg := derivative_integrable u
  have hi := kernel_smul_integrable hg measurable_meanKernel meanKernel_bound
  have hni := hi.norm
  rw [l1Norm, ← integral_intervalMeasure]
  calc
    _ ≤ ∫ x, ∫ t, ‖meanKernel x t • g t‖ ∂intervalMeasure ∂intervalMeasure := by
      apply integral_mono_ae ((representative_continuous hf).sub continuousOn_const).norm.integrableOn_Icc
        hi.integral_norm_prod_left
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      change ‖f x - mean f‖ ≤ _
      rw [mean_kernel_formula hf hx]
      exact norm_integral_le_integral_norm _
    _ = ∫ t, ∫ x, ‖meanKernel x t • g t‖ ∂intervalMeasure ∂intervalMeasure :=
      integral_integral_swap (f := fun x t => ‖meanKernel x t • g t‖) hni
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp_rw [norm_smul, Real.norm_eq_abs]
      rw [integral_mul_const, integral_abs_meanKernel ht]


theorem parabola_le_half (t : ℝ) : 2 * t * (1 - t) ≤ (1 / 2 : ℝ) := by
  nlinarith [sq_nonneg (t - 1 / 2)]

theorem weighted_derivative_integrable (u : W11 𝕜) :
    Integrable (fun t => (2 * t * (1 - t)) * ‖lineFunction (derivativeLp u) t‖)
      intervalMeasure := by
  apply (derivative_integrable u).norm.bdd_mul (c := 1 / 2)
    (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hn : 0 ≤ 2 * t * (1 - t) := mul_nonneg (mul_nonneg (by norm_num) ht.1) (sub_nonneg.mpr ht.2)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact parabola_le_half t

theorem derivative_norm_integral (u : W11 𝕜) :
    (∫ t, ‖lineFunction (derivativeLp u) t‖ ∂intervalMeasure) = ‖derivativeLp u‖ :=
  (integral_intervalMeasure _).trans (derivative_l1Norm u)

theorem weighted_derivative_le (u : W11 𝕜) :
    (∫ t, (2 * t * (1 - t)) * ‖lineFunction (derivativeLp u) t‖ ∂intervalMeasure) ≤
      (1 / 2 : ℝ) * ‖derivativeLp u‖ := by
  have h := integral_mono (weighted_derivative_integrable u)
    ((derivative_integrable u).norm.const_mul (1 / 2))
    (fun t => mul_le_mul_of_nonneg_right (parabola_le_half t) (norm_nonneg _))
  rw [integral_const_mul, derivative_norm_integral] at h
  exact h

theorem mean_l1_bound : Specs.ExpandedFA.PartIV.IntervalL1Constants.MeanL1Bound := by
  intro 𝕜 _ u f hf
  exact (mean_l1_weighted_bound hf).trans (weighted_derivative_le u)

theorem weighted_derivative_lt {u : W11 𝕜} (hu : 0 < ‖derivativeLp u‖) :
    (∫ t, (2 * t * (1 - t)) * ‖lineFunction (derivativeLp u) t‖ ∂intervalMeasure) <
      (1 / 2 : ℝ) * ‖derivativeLp u‖ := by
  apply lt_of_le_of_ne (weighted_derivative_le u)
  intro heq
  have heq' : (∫ t, (2 * t * (1 - t)) * ‖lineFunction (derivativeLp u) t‖ ∂intervalMeasure) =
      ∫ t, (1 / 2 : ℝ) * ‖lineFunction (derivativeLp u) t‖ ∂intervalMeasure := by
    rw [integral_const_mul, derivative_norm_integral]
    exact heq
  have ha := (integral_eq_iff_of_ae_le (weighted_derivative_integrable u)
    ((derivative_integrable u).norm.const_mul (1 / 2))
    (Filter.Eventually.of_forall (fun t =>
      mul_le_mul_of_nonneg_right (parabola_le_half t) (norm_nonneg _)))).mp heq'
  have hz : (fun t => ‖lineFunction (derivativeLp u) t‖) =ᵐ[intervalMeasure] 0 := by
    have hn : ∀ᵐ t ∂intervalMeasure, t ≠ (1 / 2 : ℝ) :=
      intervalMeasure.ae_ne _
    filter_upwards [ha, hn] with t ht htn
    change (2 * t * (1 - t)) * ‖lineFunction (derivativeLp u) t‖ =
      (1 / 2 : ℝ) * ‖lineFunction (derivativeLp u) t‖ at ht
    have hs : 0 < (t - 1 / 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr htn)
    have hn := norm_nonneg (lineFunction (derivativeLp u) t)
    change ‖lineFunction (derivativeLp u) t‖ = 0
    nlinarith
  have hi := integral_congr_ae hz
  rw [integral_intervalMeasure, show (∫ t in (0 : ℝ)..1, ‖lineFunction (derivativeLp u) t‖) = ‖derivativeLp u‖ from derivative_l1Norm u] at hi
  simp only [Pi.zero_apply, integral_zero] at hi
  exact (ne_of_gt hu) hi

theorem mean_l1_strict : Specs.ExpandedFA.PartIV.IntervalL1Constants.MeanL1Strict := by
  intro 𝕜 _ u f hf hn
  exact (mean_l1_weighted_bound hf).trans_lt (weighted_derivative_lt (derivative_norm_pos hf hn))


/-- A bounded-interval Lipschitz function is realized in the actual Sobolev
graph. The additional a.e. identity records its exact weak derivative. -/
theorem lipschitz_realization {f : ℝ → 𝕜} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ u : W11 𝕜, PrimitiveRepresentative u f ∧
      lineFunction (derivativeLp u) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] deriv f := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf.continuous.continuousOn.norm
  have hfm : MemLp f 1 (volume.restrict (Ioo (0 : ℝ) 1)) := by
    apply MemLp.of_bound hf.continuous.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hB ⟨x, Ioo_subset_Icc_self hx, rfl⟩
  have hgm : MemLp (deriv f) 1 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    MemLp.of_bound (aestronglyMeasurable_deriv f _) K
      (Filter.Eventually.of_forall (fun _ => norm_deriv_le_of_lipschitz hf))
  let hvm := hfm.comp_measurePreserving (coordinate_measurePreserving unitInterval)
  let hwm := hgm.comp_measurePreserving (coordinate_measurePreserving unitInterval)
  let v := hvm.toLp (fun z : ExpandedFA.Distributions.Domain 1 => f (z 0))
  let w := hwm.toLp (fun z : ExpandedFA.Distributions.Domain 1 => deriv f (z 0))
  have hv : Represents v f := hvm.coeFn_toLp
  have hw : w =ᵐ[volume.restrict (lineDomain unitInterval :
      Set (ExpandedFA.Distributions.Domain 1))] (fun z => deriv f (z 0)) := hwm.coeFn_toLp
  have hd : ExpandedFA.Sobolev.lpDistribution w =
      -(ExpandedFA.Sobolev.lpDistribution v).comp
        (ExpandedFA.Distributions.testPartialCLM [0]) := by
    ext φ
    simp only [ExpandedFA.Sobolev.lpDistribution_apply, neg_apply, ContinuousLinearMap.comp_apply]
    change (∫ z, φ z * w z ∂volume.restrict (lineDomain unitInterval :
      Set (ExpandedFA.Distributions.Domain 1))) =
      -(∫ z, ExpandedFA.Distributions.testPartialCLM [0] φ z * v z
        ∂volume.restrict (lineDomain unitInterval : Set (ExpandedFA.Distributions.Domain 1)))
    calc
      _ = ∫ z, φ z * deriv f (z 0) ∂volume.restrict (lineDomain unitInterval :
          Set (ExpandedFA.Distributions.Domain 1)) := integral_congr_ae (hw.mono (fun _ h => by rw [h]))
      _ = _ := by
        rw [integral_test_mul_deriv_lipschitzOn hf.lipschitzOnWith]
        congr 1
        apply integral_congr_ae
        exact hv.symm.mono (fun z h => congrArg (fun c => ExpandedFA.Distributions.testPartialCLM [0] φ z * c) h)
  let u : W11 𝕜 := ofWeakDerivative v w hd
  have hu : baseLp u = v := ofWeakDerivative_base _ _ _
  have hdu : derivativeLp u = w := ofWeakDerivative_derivative _ _ _
  obtain ⟨F, hF⟩ := representative_existence 𝕜 unitInterval ordConnected_Ioo 1 u
  have he := representative_uniqueness 𝕜 unitInterval 1 v F f
    hF.1 hf.continuous.continuousOn (hu ▸ hF.2.1) hv
  refine ⟨u, ⟨hf.continuous.continuousOn, hu.symm ▸ hv, ?_, ?_⟩, ?_⟩
  · intro a _ b _
    exact hf.lipschitzOnWith.absolutelyContinuousOnInterval
  · intro x hx y hy
    rw [← he hx, ← he hy]
    exact hF.2.2.2 x hx y hy
  · rw [hdu]
    exact (linePoint_measurePreserving unitInterval).quasiMeasurePreserving.ae hw


/-- A clipped linear ramp. Its derivative is supported on (a,b). -/
def ramp (a b x : ℝ) : ℝ := min (max (x - a) 0) (b - a)

theorem ramp_lipschitz (a b : ℝ) : LipschitzWith 1 (ramp a b) := by
  have hs : LipschitzWith 1 (fun x : ℝ => x - a) := by
    simpa using (LipschitzWith.id.sub (LipschitzWith.const a))
  exact (hs.max_const 0).min_const (b - a)

theorem ramp_left {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) : ramp a b x = 0 := by
  simp [ramp, max_eq_right (sub_nonpos.mpr hx), min_eq_left (sub_nonneg.mpr hab)]

theorem ramp_middle {a b x : ℝ} (hx : a ≤ x) (hx' : x ≤ b) : ramp a b x = x - a := by
  simp [ramp, max_eq_left (sub_nonneg.mpr hx), min_eq_left (sub_le_sub_right hx' a)]

theorem ramp_right {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) : ramp a b x = b - a := by
  simp [ramp, max_eq_left (sub_nonneg.mpr (hab.trans hx)), min_eq_right (sub_le_sub_right hx a)]

theorem ramp_hasDerivAt {a b x : ℝ} (hab : a < b) (ha : x ≠ a) (hb : x ≠ b) :
    HasDerivAt (ramp a b) (if x ∈ Ioo a b then 1 else 0) x := by
  by_cases hxa : x < a
  · have hd := hasDerivAt_const x (0 : ℝ)
    have he : ramp a b =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hxa] with y hy
      exact ramp_left hab.le hy.le
    simpa [show x ∉ Ioo a b from fun h => (h.1.trans hxa).false] using
      hd.congr_of_eventuallyEq he
  · have hax : a < x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm ha)
    by_cases hxb : x < b
    · have he : ramp a b =ᶠ[𝓝 x] (fun y => y - a) := by
        filter_upwards [Ioo_mem_nhds hax hxb] with y hy
        exact ramp_middle hy.1.le hy.2.le
      simpa [show x ∈ Ioo a b from ⟨hax, hxb⟩] using
        ((hasDerivAt_id x).sub_const a).congr_of_eventuallyEq he
    · have hbx : b < x := lt_of_le_of_ne (le_of_not_gt hxb) (Ne.symm hb)
      have he : ramp a b =ᶠ[𝓝 x] (fun _ => b - a) := by
        filter_upwards [Ioi_mem_nhds hbx] with y hy
        exact ramp_right hab.le hy.le
      simpa [show x ∉ Ioo a b from fun h => (h.2.trans hbx).false] using
        (hasDerivAt_const x (b - a)).congr_of_eventuallyEq he

/-- The ramp is an actual W¹,¹ element, with exactly its expected variation. -/
theorem ramp_realization {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    ∃ u : W11 ℝ, PrimitiveRepresentative u (ramp a b) ∧ ‖derivativeLp u‖ = b - a := by
  obtain ⟨u, hu, hd⟩ := lipschitz_realization (ramp_lipschitz a b)
  refine ⟨u, hu, ?_⟩
  have he : (fun t => ‖lineFunction (derivativeLp u) t‖) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (Ioo a b).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hd, (volume.restrict (Ioo (0 : ℝ) 1)).ae_ne a,
      (volume.restrict (Ioo (0 : ℝ) 1)).ae_ne b] with t ht hta htb
    rw [ht, (ramp_hasDerivAt hab hta htb).deriv]
    by_cases h : t ∈ Ioo a b <;> simp [h]
  rw [← derivative_l1Norm u, l1Norm, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_congr_ae he,
    integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo a b ∩ Ioo (0 : ℝ) 1 = Ioo a b := by
    apply inter_eq_left.mpr
    intro x hx
    exact ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩
  rw [hs]
  simp [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]


/-- Real sharpness examples embed isometrically in either scalar field,
including their actual weak derivative norms. -/
theorem real_representative_lift (𝕜 : Type) [RCLike 𝕜]
    {u : W11 ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : PrimitiveRepresentative u f) (hL : LipschitzWith K f) :
    ∃ v : W11 𝕜, PrimitiveRepresentative v (fun x => (f x : 𝕜)) ∧
      ‖derivativeLp v‖ = ‖derivativeLp u‖ := by
  have hLK : LipschitzWith K (fun x => (f x : 𝕜)) := by
    simpa only [one_mul, Function.comp_def, RCLike.ofReal] using (RCLike.lipschitzWith_ofReal (K := 𝕜)).comp hL
  obtain ⟨v, hv, _⟩ := lipschitz_realization hLK
  refine ⟨v, hv, ?_⟩
  have he : (fun t => ‖lineFunction (derivativeLp v) t‖) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (fun t => ‖lineFunction (derivativeLp u) t‖) := by
    filter_upwards [primitive_ae_hasDerivAt hf, primitive_ae_hasDerivAt hv] with t ht htv
    have hd := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt t ht
    have he := htv.unique hd
    change lineFunction (derivativeLp v) t = ((lineFunction (𝕜 := ℝ) (derivativeLp u) t : ℝ) : 𝕜) at he
    rw [he, RCLike.norm_ofReal, Real.norm_eq_abs]
  rw [← derivative_l1Norm v, ← derivative_l1Norm u, l1Norm, l1Norm,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact integral_congr_ae he

theorem mean_ofReal (f : ℝ → ℝ) : mean (fun x => (f x : 𝕜)) = ((mean (𝕜 := ℝ) f : ℝ) : 𝕜) :=
  RCLike.intervalIntegral_ofReal

theorem supNorm_ofReal (f : ℝ → ℝ) : supNorm (fun x => (f x : 𝕜)) = supNorm f := by
  simp only [supNorm, RCLike.norm_ofReal, Real.norm_eq_abs]

theorem mean_supNorm_ofReal (f : ℝ → ℝ) :
    supNorm (fun x => (f x : 𝕜) - mean (fun x => (f x : 𝕜))) =
      supNorm (fun x => f x - mean f) := by
  rw [mean_ofReal]
  simp only [← RCLike.ofReal_sub, supNorm_ofReal]

theorem mean_l1Norm_ofReal (f : ℝ → ℝ) :
    l1Norm (fun x => (f x : 𝕜) - mean (fun x => (f x : 𝕜))) =
      l1Norm (fun x => f x - mean f) := by
  rw [mean_ofReal]
  simp only [← RCLike.ofReal_sub, l1Norm, RCLike.norm_ofReal, Real.norm_eq_abs]

/-- The mean of a clipped ramp, obtained by its three linear pieces. -/
theorem mean_ramp {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    mean (ramp a b) = (b - a) * (1 - (a + b) / 2) := by
  have hi (c d : ℝ) : IntervalIntegrable (ramp a b) volume c d :=
    (ramp_lipschitz a b).continuous.intervalIntegrable _ _
  have hleft : (∫ x in (0 : ℝ)..a, ramp a b x) = 0 := by
    calc
      _ = ∫ _ in (0 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le ha]
        intro x hx
        exact ramp_left hab hx.2
      _ = 0 := by simp
  have hmiddle : (∫ x in a..b, ramp a b x) = (b - a) ^ 2 / 2 := by
    calc
      _ = ∫ x in a..b, x - a := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hab]
        intro x hx
        exact ramp_middle hx.1 hx.2
      _ = _ := by
        rw [intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => a)
          (continuous_id.intervalIntegrable _ _) intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have hright : (∫ x in b..(1 : ℝ), ramp a b x) = (1 - b) * (b - a) := by
    calc
      _ = ∫ _ in b..(1 : ℝ), b - a := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hb]
        intro x hx
        exact ramp_right hab hx.1
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]
  unfold mean
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b 1),
    hleft, hmiddle, hright]
  ring


theorem mean_sup_sharp_real (C : ℝ) (hC : C < 1) :
    ∃ (u : W11 ℝ) (f : ℝ → ℝ), PrimitiveRepresentative u f ∧
      LipschitzWith 1 f ∧ 0 < ‖derivativeLp u‖ ∧
      C * ‖derivativeLp u‖ < supNorm (fun x => f x - mean f) := by
  let e := min (1 - C) 1
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he1 : e ≤ 1 := min_le_right _ _
  have heC : e ≤ 1 - C := min_le_left _ _
  obtain ⟨u, hu, hd⟩ := ramp_realization (a := 0) (b := e) (by norm_num) he1 he
  have hm : mean (ramp 0 e) = e * (1 - e / 2) := by
    simpa using mean_ramp (a := 0) (b := e) (by norm_num) he1 he.le
  have hmp : 0 < mean (ramp 0 e) := by rw [hm]; exact mul_pos he (by linarith)
  have hs := norm_le_supNorm (f := fun x => ramp 0 e x - mean (ramp 0 e))
    ((ramp_lipschitz 0 e).continuous.continuousOn.sub continuousOn_const)
    (x := 0) (by norm_num)
  change ‖ramp 0 e 0 - mean (ramp 0 e)‖ ≤ _ at hs
  rw [ramp_left he.le (le_refl 0), zero_sub, norm_neg,
    Real.norm_of_nonneg hmp.le] at hs
  refine ⟨u, ramp 0 e, hu, ramp_lipschitz 0 e, ?_, ?_⟩
  · simpa [hd] using he
  · rw [hd, sub_zero]
    have hratio : C < 1 - e / 2 := by linarith
    calc
      C * e < e * (1 - e / 2) := by
        nlinarith [mul_lt_mul_of_pos_right hratio he]
      _ = mean (ramp 0 e) := hm.symm
      _ ≤ _ := hs

theorem mean_sup_sharp : Specs.ExpandedFA.PartIV.IntervalL1Constants.MeanSupSharp := by
  intro 𝕜 _ C hC
  obtain ⟨u, f, hf, hL, hd, hs⟩ := mean_sup_sharp_real C hC
  obtain ⟨v, hv, he⟩ := real_representative_lift 𝕜 hf hL
  refine ⟨v, (fun x => (f x : 𝕜)), hv, ?_, ?_⟩
  · rwa [he]
  · rwa [he, mean_supNorm_ofReal]

/-- The centered ramp approaches a step at 1/2. Its exact deviation norm
makes the sharpness limit an elementary inequality. -/
theorem centered_ramp_l1 {d : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2) :
    l1Norm (fun x => ramp (1 / 2 - d) (1 / 2 + d) x -
      mean (ramp (1 / 2 - d) (1 / 2 + d))) = d - d ^ 2 := by
  let a := 1 / 2 - d
  let b := 1 / 2 + d
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : b ≤ 1 := by dsimp [b]; linarith
  have hac : a ≤ 1 / 2 := by dsimp [a]; linarith
  have hcb : 1 / 2 ≤ b := by dsimp [b]; linarith
  have hab : a ≤ b := hac.trans hcb
  have hm : mean (ramp a b) = d := by
    rw [mean_ramp ha hb hab]
    dsimp [a, b]
    ring
  have hi (c e : ℝ) : IntervalIntegrable (fun x => ‖ramp a b x - d‖) volume c e :=
    (((ramp_lipschitz a b).continuous.sub continuous_const).norm).intervalIntegrable _ _
  have h0 : (∫ x in (0 : ℝ)..a, ‖ramp a b x - d‖) = a * d := by
    calc
      _ = ∫ _ in (0 : ℝ)..a, d := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le ha]
        intro x hx
        change ‖ramp a b x - d‖ = d
        rw [ramp_left hab hx.2, zero_sub, norm_neg, Real.norm_of_nonneg hd.le]
      _ = _ := by simp [smul_eq_mul]
  have h1 : (∫ x in a..(1 / 2 : ℝ), ‖ramp a b x - d‖) = d ^ 2 / 2 := by
    calc
      _ = ∫ x in a..(1 / 2 : ℝ), 1 / 2 - x := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hac]
        intro x hx
        change ‖ramp a b x - d‖ = 1 / 2 - x
        rw [ramp_middle hx.1 (hx.2.trans hcb),
          Real.norm_of_nonpos (by dsimp [a]; linarith [hx.2])]
        dsimp [a]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 / 2 : ℝ)) (g := fun x : ℝ => x)
          intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
          intervalIntegral.integral_const, integral_id]
        simp only [smul_eq_mul]
        dsimp [a]
        ring
  have h2 : (∫ x in (1 / 2 : ℝ)..b, ‖ramp a b x - d‖) = d ^ 2 / 2 := by
    calc
      _ = ∫ x in (1 / 2 : ℝ)..b, x - 1 / 2 := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hcb]
        intro x hx
        change ‖ramp a b x - d‖ = x - 1 / 2
        rw [ramp_middle (hac.trans hx.1) hx.2,
          Real.norm_of_nonneg (by dsimp [a]; linarith [hx.1])]
        dsimp [a]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => (1 / 2 : ℝ))
          (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_const, integral_id]
        simp only [smul_eq_mul]
        dsimp [b]
        ring
  have h3 : (∫ x in b..(1 : ℝ), ‖ramp a b x - d‖) = (1 - b) * d := by
    calc
      _ = ∫ _ in b..(1 : ℝ), d := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hb]
        intro x hx
        change ‖ramp a b x - d‖ = d
        rw [ramp_right hab hx.1, show b - a - d = d by dsimp [a, b]; ring,
          Real.norm_of_nonneg hd.le]
      _ = _ := by simp [smul_eq_mul]
  change (∫ x in (0 : ℝ)..1, ‖ramp a b x - mean (ramp a b)‖) = _
  rw [hm, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hi a (1 / 2)) (hi (1 / 2) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (1 / 2) b) (hi b 1), h0, h1, h2, h3]
  dsimp [a, b]
  ring

theorem mean_l1_sharp_real (C : ℝ) (hC : C < 1 / 2) :
    ∃ (u : W11 ℝ) (f : ℝ → ℝ), PrimitiveRepresentative u f ∧
      LipschitzWith 1 f ∧ 0 < ‖derivativeLp u‖ ∧
      C * ‖derivativeLp u‖ < l1Norm (fun x => f x - mean f) := by
  let d := min (1 / 2 - C) (1 / 4)
  have hd : 0 < d := lt_min (by linarith) (by norm_num)
  have hdh : d ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hdC : d ≤ 1 / 2 - C := min_le_left _ _
  obtain ⟨u, hu, he⟩ := ramp_realization (a := 1 / 2 - d) (b := 1 / 2 + d)
    (by linarith) (by linarith) (by linarith)
  have hn : ‖derivativeLp u‖ = 2 * d := by rw [he]; ring
  refine ⟨u, _, hu, ramp_lipschitz _ _, ?_, ?_⟩
  · rw [hn]; positivity
  · rw [hn, centered_ramp_l1 hd hdh]
    have hr : 2 * C < 1 - d := by linarith
    have := mul_lt_mul_of_pos_right hr hd
    nlinarith

theorem mean_l1_sharp : Specs.ExpandedFA.PartIV.IntervalL1Constants.MeanL1Sharp := by
  intro 𝕜 _ C hC
  obtain ⟨u, f, hf, hL, hd, hs⟩ := mean_l1_sharp_real C hC
  obtain ⟨v, hv, he⟩ := real_representative_lift 𝕜 hf hL
  refine ⟨v, (fun x => (f x : 𝕜)), hv, ?_, ?_⟩
  · rwa [he]
  · rwa [he, mean_l1Norm_ofReal]


def triangularTent (x : ℝ) : ℝ := min x (1 - x)

theorem triangularTent_lipschitz : LipschitzWith 1 triangularTent := by
  have h : LipschitzWith 1 (fun x : ℝ => 1 - x) := by
    simpa using (LipschitzWith.const (1 : ℝ)).sub LipschitzWith.id
  change LipschitzWith 1 (fun x : ℝ => min x (1 - x))
  simpa using LipschitzWith.id.min h

theorem triangularTent_optimizer : NonnegativeUnimodalTent triangularTent := by
  refine ⟨by norm_num [triangularTent], by norm_num [triangularTent], ?_, ?_,
    1 / 2, by norm_num, ?_, ?_⟩
  · intro x hx
    exact le_min hx.1 (sub_nonneg.mpr hx.2)
  · exact ⟨1 / 2, by norm_num, by norm_num [triangularTent]⟩
  · intro x hx y hy hxy
    dsimp [triangularTent]
    rw [min_eq_left (by linarith [hx.2]), min_eq_left (by linarith [hy.2])]
    exact hxy
  · intro x hx y hy hxy
    dsimp [triangularTent]
    rw [min_eq_right (show 1 - y ≤ y by linarith [hy.1]),
      min_eq_right (show 1 - x ≤ x by linarith [hx.1])]
    linarith

theorem zero_sup_sharp : Specs.ExpandedFA.PartIV.IntervalL1Constants.ZeroSupSharp := by
  intro 𝕜 _ C hC
  obtain ⟨u, hu, _⟩ := lipschitz_realization triangularTent_lipschitz
  obtain ⟨hz, hd, hs⟩ := tent_equality u triangularTent hu triangularTent_optimizer
  obtain ⟨v, hv, he⟩ := real_representative_lift 𝕜 hu triangularTent_lipschitz
  refine ⟨v, (fun x => (triangularTent x : 𝕜)), hv, ?_, ?_, ?_⟩
  · apply ExpandedFA.Sobolev.Trace.interval_zeroSpace_of_endpoints (by norm_num)
      (by norm_num : (0 : ℝ) < 1) v _ hv
    · norm_num [triangularTent]
    · norm_num [triangularTent]
  · rwa [he]
  · rw [he, supNorm_ofReal, hs]
    exact mul_lt_mul_of_pos_right hC hd

end ExpandedFA.PartIV.IntervalL1
