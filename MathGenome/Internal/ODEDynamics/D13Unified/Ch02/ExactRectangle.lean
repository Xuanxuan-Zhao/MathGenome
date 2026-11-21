import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.ExactRectangle
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace D13Unified.ExactRectangle
open Specs.D13Unified.Ch02.ExactRectangle

/-- The potential prescribed in Proposition d13:02:exact. -/
def potential : potentialType := potentialValue

variable {I J : OpenTimeInterval} {P Q : ℝ × ℝ → ℝ}

lemma timePartial_continuousOn
    (hP : ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier)) :
    ContinuousOn (timePartial P) (I.carrier ×ˢ J.carrier) :=
  (hP.continuousOn_fderiv_of_isOpen (I.isOpen.prod J.isOpen) le_rfl).clm_apply
    continuousOn_const

lemma statePartial_continuousOn
    (hP : ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier)) :
    ContinuousOn (statePartial P) (I.carrier ×ˢ J.carrier) :=
  (hP.continuousOn_fderiv_of_isOpen (I.isOpen.prod J.isOpen) le_rfl).clm_apply
    continuousOn_const

lemma hasDerivAt_time
    (hP : ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier))
    {t x : ℝ} (ht : t ∈ I.carrier) (hx : x ∈ J.carrier) :
    HasDerivAt (fun r => P (r, x)) (timePartial P (t, x)) t := by
  exact ((hP.differentiableOn one_ne_zero).differentiableAt
    ((I.isOpen.prod J.isOpen).mem_nhds ⟨ht, hx⟩)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

lemma hasDerivAt_state
    (hP : ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier))
    {t x : ℝ} (ht : t ∈ I.carrier) (hx : x ∈ J.carrier) :
    HasDerivAt (fun v => P (t, v)) (statePartial P (t, x)) x := by
  exact ((hP.differentiableOn one_ne_zero).differentiableAt
    ((I.isOpen.prod J.isOpen).mem_nhds ⟨ht, hx⟩)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))

lemma continuousOn_time_slice {H : ℝ × ℝ → ℝ}
    (hH : ContinuousOn H (I.carrier ×ˢ J.carrier))
    {x : ℝ} (hx : x ∈ J.carrier) : ContinuousOn (fun t => H (t, x)) I.carrier :=
  hH.comp (continuousOn_id.prodMk continuousOn_const) (fun _ ht => ⟨ht, hx⟩)

lemma continuousOn_state_slice {H : ℝ × ℝ → ℝ}
    (hH : ContinuousOn H (I.carrier ×ˢ J.carrier))
    {t : ℝ} (ht : t ∈ I.carrier) : ContinuousOn (fun x => H (t, x)) J.carrier :=
  hH.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => ⟨ht, hx⟩)

/-- Compactness provides one derivative bound for a whole time neighbourhood
and the entire (possibly oppositely oriented) state integration segment. -/
lemma hasDerivAt_parameter_integral
    (hQ : ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier))
    {t ξ x : ℝ} (ht : t ∈ I.carrier) (hξ : ξ ∈ J.carrier) (hx : x ∈ J.carrier) :
    HasDerivAt (fun r => ∫ v in ξ..x, Q (r, v))
      (∫ v in ξ..x, timePartial Q (t, v)) t := by
  obtain ⟨a, b, _, hB, hBI⟩ := exists_Icc_mem_subset_of_mem_nhds (I.isOpen.mem_nhds ht)
  have hseg := J.ordConnected.uIcc_subset hξ hx
  have hc := timePartial_continuousOn hQ
  have hbox : Icc a b ×ˢ uIcc ξ x ⊆ I.carrier ×ˢ J.carrier :=
    prod_mono hBI hseg
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    (hc.mono hbox)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun r v => timePartial Q (r, v)) (bound := fun _ => C) hB ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [I.isOpen.mem_nhds ht] with r hr
    exact ((continuousOn_state_slice hQ.continuousOn hr).mono
      (uIoc_subset_uIcc.trans hseg)).aestronglyMeasurable measurableSet_uIoc
  · exact ((continuousOn_state_slice hQ.continuousOn ht).mono hseg).intervalIntegrable
  · exact ((continuousOn_state_slice hc ht).mono
      (uIoc_subset_uIcc.trans hseg)).aestronglyMeasurable measurableSet_uIoc
  · exact Eventually.of_forall fun v hv r hr => hC (r, v) ⟨hr, uIoc_subset_uIcc hv⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun v hv r hr =>
      hasDerivAt_time hQ (hBI hr) (hseg (uIoc_subset_uIcc hv))

lemma integral_timePartial_eq
    (hP : ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier))
    (hclosed : ∀ p ∈ I.carrier ×ˢ J.carrier, statePartial P p = timePartial Q p)
    {t ξ x : ℝ} (ht : t ∈ I.carrier) (hξ : ξ ∈ J.carrier) (hx : x ∈ J.carrier) :
    (∫ v in ξ..x, timePartial Q (t, v)) = P (t, x) - P (t, ξ) := by
  have hseg := J.ordConnected.uIcc_subset hξ hx
  have heq : EqOn (fun v => timePartial Q (t, v))
      (fun v => statePartial P (t, v)) (uIcc ξ x) :=
    fun v hv => (hclosed (t, v) ⟨ht, hseg hv⟩).symm
  rw [intervalIntegral.integral_congr heq]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => hasDerivAt_state hP ht (hseg hv))
    (((continuousOn_state_slice (statePartial_continuousOn hP) ht).mono hseg).intervalIntegrable)

theorem potential_partials : potentialPartialsExpected := by
  intro I J P Q hP hQ hclosed s hs ξ hξ t ht x hx
  have hPt := continuousOn_time_slice hP.continuousOn hξ
  have hQx := continuousOn_state_slice hQ.continuousOn ht
  constructor
  · have h₁ := intervalIntegral.integral_hasDerivAt_right
      ((hPt.mono (I.ordConnected.uIcc_subset hs ht)).intervalIntegrable)
      (hPt.stronglyMeasurableAtFilter I.isOpen t ht)
      (hPt.continuousAt (I.isOpen.mem_nhds ht))
    have h₂ := hasDerivAt_parameter_integral hQ ht hξ hx
    rw [integral_timePartial_eq hP hclosed ht hξ hx] at h₂
    convert h₁.add h₂ using 1 <;> first | rfl | ring
  · simpa only [potentialValue] using (intervalIntegral.integral_hasDerivAt_right
      ((hQx.mono (J.ordConnected.uIcc_subset hξ hx)).intervalIntegrable)
      (hQx.stronglyMeasurableAtFilter J.isOpen x hx)
      (hQx.continuousAt (J.isOpen.mem_nhds hx))).const_add (∫ r in s..t, P (r, ξ))

/-- The potential has the differential P dt + Q dx on the rectangle. -/
lemma potential_hasFDerivAt
    (hP : ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier))
    (hQ : ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier))
    (hclosed : ∀ p ∈ I.carrier ×ˢ J.carrier, statePartial P p = timePartial Q p)
    {s ξ : ℝ} (hs : s ∈ I.carrier) (hξ : ξ ∈ J.carrier)
    {p : ℝ × ℝ} (hp : p ∈ I.carrier ×ˢ J.carrier) :
    HasFDerivAt (potentialValue P Q s ξ)
      ((ContinuousLinearMap.toSpanSingleton ℝ (P p)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (Q p))) p := by
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod (u := p)
    (f := fun t x => potentialValue P Q s ξ (t, x))
    (f₁ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (P (t, x)))
    (f₂ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (Q (t, x)))
  · filter_upwards [(I.isOpen.prod J.isOpen).mem_nhds hp] with q hq
    exact (potential_partials I J P Q hP hQ hclosed s hs ξ hξ q.1 hq.1 q.2 hq.2).1.hasFDerivAt
  · filter_upwards [(I.isOpen.prod J.isOpen).mem_nhds hp] with q hq
    exact (potential_partials I J P Q hP hQ hclosed s hs ξ hξ q.1 hq.1 q.2 hq.2).2.hasFDerivAt
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      (hP.continuousOn.continuousAt ((I.isOpen.prod J.isOpen).mem_nhds hp))
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      (hQ.continuousOn.continuousAt ((I.isOpen.prod J.isOpen).mem_nhds hp))

lemma potential_graph_hasDerivAt
    (hP : ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier))
    (hQ : ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier))
    (hclosed : ∀ p ∈ I.carrier ×ˢ J.carrier, statePartial P p = timePartial Q p)
    {s ξ : ℝ} (hs : s ∈ I.carrier) (hξ : ξ ∈ J.carrier)
    {x : ℝ → ℝ} {t v : ℝ} (hx : HasDerivAt x v t)
    (hgraph : (t, x t) ∈ I.carrier ×ˢ J.carrier) :
    HasDerivAt (fun r => potentialValue P Q s ξ (r, x r))
      (P (t, x t) + Q (t, x t) * v) t := by
  have hg : HasDerivAt (fun r => (r, x r)) (1, v) t :=
    (hasDerivAt_id t).prodMk hx
  have hd := (potential_hasFDerivAt hP hQ hclosed hs hξ hgraph).comp_hasDerivAt t hg
  simpa [ContinuousLinearMap.coprod_apply, mul_comm] using! hd

theorem potential_graph_iff : graphIffExpected := by
  intro I J P Q hP hQ hclosed s hs ξ hξ K x hx hg
  have hd : ∀ t ∈ K.carrier, HasDerivAt
      (fun r => potentialValue P Q s ξ (r, x r))
      (P (t, x t) + Q (t, x t) * deriv x t) t := by
    intro t ht
    exact potential_graph_hasDerivAt hP hQ hclosed hs hξ
      (((hx.differentiableOn one_ne_zero).differentiableAt
        (K.isOpen.mem_nhds ht)).hasDerivAt) (hg t ht)
  constructor
  · intro heq
    exact K.isOpen.exists_is_const_of_deriv_eq_zero K.ordConnected.isPreconnected
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hd t ht).deriv.trans (heq t ht))
  · rintro ⟨c, hc⟩ t ht
    have hconst : HasDerivAt (fun r => potentialValue P Q s ξ (r, x r)) 0 t := by
      apply (hasDerivAt_const t c).congr_of_eventuallyEq
      filter_upwards [K.isOpen.mem_nhds ht] with r hr
      exact hc r hr
    exact (hd t ht).unique hconst

theorem normal_form_iff : normalFormExpected := by
  intro P Q v hQ
  rw [eq_div_iff hQ]
  constructor <;> intro h <;> nlinarith

theorem potential_graph_normal_form_iff : graphNormalFormExpected := by
  intro I J P Q hP hQ hclosed s hs ξ hξ K x hx hg hQ0
  rw [← potential_graph_iff I J P Q hP hQ hclosed s hs ξ hξ K x hx hg]
  exact forall₂_congr fun t ht => (normal_form_iff _ _ _ (hQ0 t ht)).symm

lemma potential_graph_hasDerivWithinAt
    (hP : ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier))
    (hQ : ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier))
    (hclosed : ∀ p ∈ I.carrier ×ˢ J.carrier, statePartial P p = timePartial Q p)
    {s ξ : ℝ} (hs : s ∈ I.carrier) (hξ : ξ ∈ J.carrier)
    {K : Set ℝ} {x : ℝ → ℝ} {t v : ℝ} (hx : HasDerivWithinAt x v K t)
    (hgraph : (t, x t) ∈ I.carrier ×ˢ J.carrier) :
    HasDerivWithinAt (fun r => potentialValue P Q s ξ (r, x r))
      (P (t, x t) + Q (t, x t) * v) K t := by
  have hg : HasDerivWithinAt (fun r => (r, x r)) (1, v) K t :=
    (hasDerivWithinAt_id t K).prodMk hx
  have hd := (potential_hasFDerivAt hP hQ hclosed hs hξ hgraph).comp_hasDerivWithinAt t hg
  simpa [ContinuousLinearMap.coprod_apply, mul_comm] using! hd

theorem potential_graph_on_interval_iff : graphOnIntervalIffExpected := by
  intro I J P Q hP hQ hclosed s hs ξ hξ K x hK hx hg
  have hconv : Convex ℝ K.carrier := K.ordConnected.convex
  have hu : UniqueDiffOn ℝ K.carrier :=
    uniqueDiffOn_convex hconv (hconv.nontrivial_iff_nonempty_interior.mp hK)
  have hd : ∀ t ∈ K.carrier, HasDerivWithinAt
      (fun r => potentialValue P Q s ξ (r, x r))
      (P (t, x t) + Q (t, x t) * derivWithin x K.carrier t) K.carrier t := by
    intro t ht
    exact potential_graph_hasDerivWithinAt hP hQ hclosed hs hξ
      ((hx.differentiableOn one_ne_zero t ht).hasDerivWithinAt) (hg t ht)
  constructor
  · intro heq
    obtain ⟨t₀, ht₀⟩ := K.nonempty
    refine ⟨potentialValue P Q s ξ (t₀, x t₀), fun t ht => ?_⟩
    apply hconv.is_const_of_fderivWithin_eq_zero
      (fun r hr => (hd r hr).differentiableWithinAt) _ ht ht₀
    intro r hr
    simpa [heq r hr] using (hd r hr).hasFDerivWithinAt.fderivWithin (hu r hr)
  · rintro ⟨c, hc⟩ t ht
    have hconst : HasDerivWithinAt (fun r => potentialValue P Q s ξ (r, x r))
        0 K.carrier t :=
      (hasDerivWithinAt_const t K.carrier c).congr_of_mem hc ht
    exact ((hd t ht).derivWithin (hu t ht)).symm.trans
      (hconst.derivWithin (hu t ht))

end D13Unified.ExactRectangle
