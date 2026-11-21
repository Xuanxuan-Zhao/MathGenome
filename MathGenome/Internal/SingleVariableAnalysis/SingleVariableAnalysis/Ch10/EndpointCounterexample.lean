import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.EndpointCounterexample
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.SeveralEndpoints
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Lagrange

/-! Linked cancellation at the endpoints of (0,1).
The compact-interval evaluation below is proved directly from real mean values
and all-tagged Darboux convergence; no measure-integral bridge is assumed. -/
noncomputable section
namespace SingleVariableAnalysis.EndpointCounterexample
open Set Filter
open scoped Topology BigOperators
open SingleVariableAnalysis.Riemann
open SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.EndpointCounterexample

def integrand : ℝ → ℝ := fun x => 1 / (1 - x) - 1 / x
def primitive : ℝ → ℝ := fun x => -seriesLog (1 - x) - seriesLog x

theorem primitive_derivative : primitiveDerivative := by
  intro x hx
  change HasDerivAt primitive (integrand x) x
  have h := (((seriesLog_hasDerivAt (1-x) (by linarith [hx.2])).comp x
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))).neg).sub
      (seriesLog_hasDerivAt x hx.1)
  convert h using 1 <;> first | rfl | simp [integrand]

private theorem integrand_continuous {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContinuousOn integrand (Icc a b) := by
  apply ContinuousOn.sub
  · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun x hx => by dsimp; linarith [hx.2])
  · exact continuousOn_const.div continuousOn_id
      (fun x hx => ne_of_gt (ha.trans_le hx.1))

/-- A continuous integrand and its real primitive give the proper Darboux value.
The mean-value tag in each cell is compared with every permitted tag. -/
theorem darboux_value_of_continuous_primitive (F f : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) :
    ∃ h : RealIntegrable f a b, realIntegral f h = F b - F a := by
  rcases hab.eq_or_lt with rfl | hab
  · exact ⟨realIntegrable_degenerate f a, by rw [realIntegral_degenerate]; ring⟩
  have hbound : BoundedOnInterval f a b :=
    ⟨isCompact_Icc.bddBelow_image hf, isCompact_Icc.bddAbove_image hf⟩
  apply (real_tagged_equivalence f hab.le hbound _).mpr
  intro ε hε
  let η := ε / (2 * (b - a))
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  refine ⟨δ, hδ, fun P ξ hP => ?_⟩
  have hcell (i : Fin P.n) : ∃ c ∈ Ioo (P.point i.castSucc) (P.point i.succ),
      F (P.point i.succ) - F (P.point i.castSucc) =
        f c * cellLength P i := by
    have hsub := cell_subset_interval P i
    obtain ⟨c, hc, heq⟩ := lagrange_deriv F _ _
      (P.strictMono (Fin.castSucc_lt_succ (i := i)))
      (fun x hx => (hd x (hsub hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (hsub ⟨hx.1.le, hx.2.le⟩)).differentiableAt)
    exact ⟨c, hc, by rw [(hd c (hsub ⟨hc.1.le, hc.2.le⟩)).deriv] at heq; exact heq⟩
  choose c hc heq using hcell
  have hsum : (∑ i : Fin P.n, f (c i) * cellLength P i) = F b - F a := by
    simp_rw [← heq]
    simpa only [P.first, P.last] using sum_cell_differences (fun j => F (P.point j))
  have hdiff (i : Fin P.n) : |f (ξ i) - f (c i)| ≤ η := by
    apply le_of_lt
    apply hclose (ξ i) (cell_subset_interval P i (ξ i).property)
      (c i) (cell_subset_interval P i ⟨(hc i).1.le, (hc i).2.le⟩)
    rw [Real.dist_eq]
    have ht := (ξ i).property
    have hm := (cellLength_le_mesh P i).trans_lt hP
    change P.point i.succ - P.point i.castSucc < δ at hm
    apply abs_lt.mpr
    constructor <;> linarith [(hc i).1, (hc i).2, ht.1, ht.2]
  rw [← hsum]
  have hs : taggedSum P ξ f - ∑ i : Fin P.n, f (c i) * cellLength P i =
      ∑ i : Fin P.n, (f (ξ i) - f (c i)) * cellLength P i := by
    simp only [taggedSum, S.sumValue, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs, Real.norm_eq_abs]
  calc
    |∑ i : Fin P.n, (f (ξ i) - f (c i)) * cellLength P i| ≤
        ∑ i : Fin P.n, |(f (ξ i) - f (c i)) * cellLength P i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n, η * cellLength P i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_pos (cell_positive P i)]
      exact mul_le_mul_of_nonneg_right (hdiff i) (cell_positive P i).le
    _ = η * (b-a) := by rw [← Finset.mul_sum, sum_cellLength]
    _ = ε / 2 := by dsimp [η]; field_simp
    _ < ε := by linarith

theorem proper_evaluation : properEvaluation := by
  intro a b ha hab hb
  exact darboux_value_of_continuous_primitive primitive integrand hab
    (integrand_continuous ha hb)
    (fun x hx => primitive_derivative x ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩)

theorem primitive_symmetry : primitiveSymmetry := by
  intro x _ _
  change primitive (1-x) = primitive x
  simp only [primitive, sub_sub_cancel]
  ring

theorem linked_zero : linkedZero := by
  intro ε hε hεh
  obtain ⟨h, heq⟩ := proper_evaluation ε (1-ε) hε (by linarith) (by linarith)
  exact ⟨h, heq.trans (by rw [primitive_symmetry ε hε (by linarith)]; ring)⟩

theorem linked_limit : linkedLimit := by
  let h := fun ε : {ε : ℝ // 0 < ε ∧ ε < 1 / 2} =>
    (linked_zero ε.val ε.property.1 ε.property.2).choose
  refine ⟨h, ?_⟩
  have heq : (fun ε => I.realIntegralValue integrandValue (h ε)) = fun _ => (0 : ℝ) := by
    funext ε
    exact (linked_zero ε.val ε.property.1 ε.property.2).choose_spec
  rw [heq]
  exact tendsto_const_nhds

theorem proper_integral_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (h : RealIntegrable integrand a b) : realIntegral integrand h = primitive b - primitive a :=
  (proper_evaluation a b ha hab hb).choose_spec

/-- An explicit logarithmic threshold, uniform for all smaller positive cutoffs. -/
theorem left_value_below (B : ℝ) : ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
    ∀ t : ℝ, 0 < t → t < r → primitive (1 / 2) - primitive t < B := by
  let r := min (1 / 4 : ℝ) (Real.exp (B - primitive (1 / 2)) / 2)
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hrh : r < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨r, hr, hrh, fun t ht htr => ?_⟩
  have hth : t < 1 / 2 := htr.trans hrh
  have hl : Real.log t < B - primitive (1 / 2) := by
    apply (Real.log_lt_iff_lt_exp ht).mpr
    have hm := htr.trans_le (min_le_right (1 / 4 : ℝ)
      (Real.exp (B - primitive (1 / 2)) / 2))
    linarith [Real.exp_pos (B - primitive (1 / 2))]
  have hn : Real.log (1 - t) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  unfold primitive
  rw [seriesLog_eq_realLog t ht, seriesLog_eq_realLog (1-t) (by linarith)]
  change Real.log t < B - primitive (1 / 2) at hl
  dsimp only [primitive] at hl
  linarith

theorem left_divergence : leftDivergence := by
  let h : LeftRegular .real integrand (0 : WithBot ℝ) (1 / 2) :=
    ⟨by norm_num, fun t => (proper_evaluation t.val (1 / 2)
      (WithBot.coe_lt_coe.mp t.property.1) t.property.2.le (by norm_num)).choose⟩
  refine ⟨h, fun B => ?_⟩
  obtain ⟨r, hr, hrh, hB⟩ := left_value_below B
  refine ⟨⟨r, WithBot.coe_lt_coe.mpr hr, hrh⟩, fun t htr => ?_⟩
  change realIntegral integrand (h.2 t) < B
  exact (proper_integral_eq (WithBot.coe_lt_coe.mp t.property.1)
    t.property.2.le (by norm_num) (h.2 t)).trans_lt
      (hB t.val (WithBot.coe_lt_coe.mp t.property.1) htr)

theorem right_divergence : rightDivergence := by
  let h : RightRegular .real integrand (1 / 2) (1 : WithTop ℝ) :=
    ⟨by norm_num, fun t => (proper_evaluation (1 / 2) t.val (by norm_num)
      t.property.1.le (WithTop.coe_lt_coe.mp t.property.2)).choose⟩
  refine ⟨h, fun B => ?_⟩
  obtain ⟨r, hr, hrh, hB⟩ := left_value_below (-B)
  refine ⟨⟨1-r, by linarith, WithTop.coe_lt_coe.mpr (by linarith)⟩, fun t hrt => ?_⟩
  have ht1 : t.val < 1 := WithTop.coe_lt_coe.mp t.property.2
  have ht0 : 0 < t.val := by linarith [t.property.1]
  have hsmall := hB (1-t.val) (by linarith) (by change 1-r < t.val at hrt; linarith)
  have hsym : primitive (1-t.val) = primitive t.val := primitive_symmetry t.val ht0 ht1
  change B < realIntegral integrand (h.2 t)
  rw [hsym] at hsmall
  exact lt_of_lt_of_eq (by linarith : B < primitive t.val - primitive (1 / 2))
    (proper_integral_eq (by norm_num) t.property.1.le ht1 (h.2 t)).symm

theorem endpoint_failure : endpointFailure := by
  have hl := left_infinite_not_converges integrand (0 : WithBot ℝ) (1 / 2)
    (Or.inr left_divergence)
  have hr := right_infinite_not_converges integrand (1 / 2) (1 : WithTop ℝ)
    (Or.inl right_divergence)
  refine ⟨hl, hr, ?_⟩
  exact no_cancellation .real integrand (0 : WithBot ℝ) (1 : WithTop ℝ)
    ⟨1 / 2, by norm_num, by norm_num⟩ (Or.inl hl)

theorem cutoff_limits : cutoffLimits := by
  let C := {ε : ℝ // 0 < ε ∧ ε < 1 / 2}
  let hl := fun ε : C => (proper_evaluation ε.val (1 / 2) ε.property.1
    ε.property.2.le (by norm_num)).choose
  let hr := fun ε : C => (proper_evaluation (1 / 2) (1-ε.val) (by norm_num)
    (by linarith [ε.property.2]) (by linarith [ε.property.1])).choose
  have hv : Tendsto (Subtype.val : C → ℝ)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  refine ⟨hl, hr, tendsto_atBot.mpr (fun B => ?_), tendsto_atTop.mpr (fun B => ?_)⟩
  · obtain ⟨r, hr0, _, hB⟩ := left_value_below B
    filter_upwards [hv.eventually (eventually_lt_nhds hr0)] with ε hε
    exact ((proper_integral_eq ε.property.1 ε.property.2.le (by norm_num) (hl ε)).trans_lt
      (hB ε.val ε.property.1 hε)).le
  · obtain ⟨r, hr0, _, hB⟩ := left_value_below (-B)
    filter_upwards [hv.eventually (eventually_lt_nhds hr0)] with ε hε
    have hb := hB ε.val ε.property.1 hε
    have hs : primitive (1-ε.val) = primitive ε.val :=
      primitive_symmetry ε.val ε.property.1 (by linarith [ε.property.2])
    have he : realIntegral integrand (hr ε) = primitive ε.val - primitive (1 / 2) :=
      (proper_integral_eq (by norm_num) (by linarith [ε.property.2])
        (by linarith [ε.property.1]) (hr ε)).trans (by rw [hs])
    exact le_of_lt (lt_of_lt_of_eq (by linarith : B < primitive ε.val - primitive (1 / 2))
      he.symm)

end SingleVariableAnalysis.EndpointCounterexample
