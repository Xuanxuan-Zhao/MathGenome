import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.PrincipalValue
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.ElementaryPrimitives
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogConstruction
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.PvCounterexample
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace SingleVariableAnalysis.Riemann.PvCounterexample
open Set Filter
open scoped Topology BigOperators
open Specs.SingleVariableAnalysis.Ch10.PvCounterexample

/-- The tagged-sum proof of Newton–Leibniz on a regular compact interval.
This helper uses the actual Darboux integral, not a total measure integral. -/
private theorem integral_of_continuous_derivative (F f : ℝ → ℝ) {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) :
    ∃ h : RealIntegrable f a b, realIntegral f h = F b - F a := by
  have hbound : BoundedOnInterval f a b :=
    ⟨(isCompact_Icc.image_of_continuousOn hf).bddBelow,
      (isCompact_Icc.image_of_continuousOn hf).bddAbove⟩
  apply (real_tagged_equivalence f hab.le hbound (F b - F a)).mpr
  intro ε hε
  let η := ε / (b-a+1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  refine ⟨δ, hδ, ?_⟩
  intro P ξ hP
  have hex (i : Fin P.n) : ∃ c ∈ Ioo (P.point i.castSucc) (P.point i.succ),
      f c * cellLength P i = F (P.point i.succ) - F (P.point i.castSucc) := by
    have hlt := P.strictMono (Fin.castSucc_lt_succ (i := i))
    have hsub := cell_subset_interval P i
    obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope F f hlt
      (fun x hx => (hd x (hsub hx)).continuousAt.continuousWithinAt)
      (fun x hx => hd x (hsub ⟨hx.1.le, hx.2.le⟩))
    exact ⟨c, hc, (eq_div_iff (sub_ne_zero.mpr hlt.ne')).mp he⟩
  choose c hc he using hex
  have htel : (∑ i : Fin P.n, f (c i) * cellLength P i) = F b - F a := by
    simp_rw [he]
    simpa only [P.first, P.last] using sum_cell_differences (fun i => F (P.point i))
  change ‖taggedSum P ξ f - (F b - F a)‖ < ε
  rw [← htel]
  have herr (i : Fin P.n) : |f (ξ i) - f (c i)| ≤ η := by
    have hdist : dist (ξ i).val (c i) < δ := by
      rw [Real.dist_eq]
      apply lt_of_le_of_lt _ ((cellLength_le_mesh P i).trans_lt hP)
      apply abs_le.mpr
      have ht := (ξ i).property
      change -(P.point i.succ - P.point i.castSucc) ≤ (ξ i).val - c i ∧
        (ξ i).val - c i ≤ P.point i.succ - P.point i.castSucc
      constructor <;> linarith [ht.1, ht.2, (hc i).1, (hc i).2]
    exact (hclose _ (cell_subset_interval P i (ξ i).property) _
      (cell_subset_interval P i ⟨(hc i).1.le, (hc i).2.le⟩) hdist).le
  calc
    _ = |∑ i : Fin P.n, (f (ξ i) - f (c i)) * cellLength P i| := by
      simp only [taggedSum, Specs.SingleVariableAnalysis.Ch08.Partitions.sumValue,
        Real.norm_eq_abs, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ ≤ ∑ i : Fin P.n, |(f (ξ i) - f (c i)) * cellLength P i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n, η * cellLength P i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_pos (cell_positive P i)]
      exact mul_le_mul_of_nonneg_right (herr i) (cell_positive P i).le
    _ = η * (b-a) := by rw [← Finset.mul_sum, sum_cellLength]
    _ < ε := by
      have heq : η * (b-a+1) = ε := div_mul_cancel₀ ε (by linarith)
      nlinarith

/-- Evaluation on any regular interval avoiding zero. -/
private theorem reciprocal_integral {a b : ℝ} (hab : a < b)
    (hz : ∀ x ∈ Icc a b, x ≠ 0) :
    ∃ h : RealIntegrable (fun x => 1 / x) a b,
      realIntegral _ h = seriesLog |b| - seriesLog |a| := by
  exact integral_of_continuous_derivative (fun x => seriesLog |x|) (fun x => 1 / x)
    hab (continuousOn_const.div continuousOn_id hz)
    (fun x hx => ElementaryPrimitives.log_abs_hasDerivAt x (hz x hx))

private theorem negative_regular (a : ℝ) (ha : a < 0) :
    E.rightRegularValue .real (fun x => 1 / x) a (0 : WithTop ℝ) := by
  refine ⟨WithTop.coe_lt_coe.mpr ha, fun t => ?_⟩
  exact (reciprocal_integral t.property.1 (fun x hx =>
    ne_of_lt (hx.2.trans_lt (WithTop.coe_lt_coe.mp t.property.2)))).choose

private theorem positive_regular (b : ℝ) (hb : 0 < b) :
    E.leftRegularValue .real (fun x => 1 / x) (0 : WithBot ℝ) b := by
  refine ⟨WithBot.coe_lt_coe.mpr hb, fun t => ?_⟩
  exact (reciprocal_integral t.property.2 (fun x hx =>
    ne_of_gt ((WithBot.coe_lt_coe.mp t.property.1).trans_le hx.1))).choose

private theorem negative_truncation (a : ℝ) (ha : a < 0)
    (h : E.rightRegularValue .real (fun x => 1 / x) a (0 : WithTop ℝ))
    (t : Specs.SingleVariableAnalysis.Ch10.OneEndpoint.rightIndexValue a (0 : WithTop ℝ)) :
    E.rightTruncationValue .real (fun x => 1 / x) a (0 : WithTop ℝ) h t =
      seriesLog (-t.val) - seriesLog (-a) := by
  have ht : t.val < 0 := WithTop.coe_lt_coe.mp t.property.2
  obtain ⟨hi, he⟩ := reciprocal_integral t.property.1
    (fun x hx => ne_of_lt (hx.2.trans_lt ht))
  change realIntegral _ (h.2 t) = _
  simp only [abs_of_neg ht, abs_of_neg ha] at he
  exact he

private theorem positive_truncation (b : ℝ) (hb : 0 < b)
    (h : E.leftRegularValue .real (fun x => 1 / x) (0 : WithBot ℝ) b)
    (t : Specs.SingleVariableAnalysis.Ch10.OneEndpoint.leftIndexValue (0 : WithBot ℝ) b) :
    E.leftTruncationValue .real (fun x => 1 / x) (0 : WithBot ℝ) b h t =
      seriesLog b - seriesLog t.val := by
  have ht : 0 < t.val := WithBot.coe_lt_coe.mp t.property.1
  obtain ⟨hi, he⟩ := reciprocal_integral t.property.2
    (fun x hx => ne_of_gt (ht.trans_le hx.1))
  change realIntegral _ (h.2 t) = _
  simp only [abs_of_pos ht, abs_of_pos hb] at he
  exact he

theorem truncation_formulas : truncationFormulas := by
  intro ε hε hε1
  have hone : seriesLog 1 = 0 := seriesLog_one
  constructor
  · obtain ⟨h, he⟩ := reciprocal_integral (show (-1 : ℝ) < -ε by linarith)
      (fun x hx => ne_of_lt (show x < 0 by linarith [hx.2]))
    refine ⟨h, ?_⟩
    change realIntegral _ h = seriesLog ε
    simpa only [abs_neg, abs_of_pos hε, abs_one, hone, sub_zero] using he
  · obtain ⟨h, he⟩ := reciprocal_integral hε1
      (fun x hx => ne_of_gt (hε.trans_le hx.1))
    refine ⟨h, ?_⟩
    change realIntegral _ h = -seriesLog ε
    simpa only [abs_of_pos hε, abs_one, hone, zero_sub] using he

theorem regular_truncations : regular :=
  ⟨negative_regular (-1) (by norm_num), positive_regular 1 zero_lt_one⟩

theorem symmetric_truncation : symmetricTruncation := by
  intro h t
  unfold P.interiorTruncationValue
  erw [negative_truncation (-1) (by norm_num), positive_truncation 1 zero_lt_one]
  simp only [zero_sub, zero_add, neg_neg]
  change (seriesLog t.val - seriesLog 1) + (seriesLog 1 - seriesLog t.val) = (0 : ℝ)
  ring

theorem principal_value_zero : principalValueZero := by
  refine ⟨regular_truncations, fun η hη => ⟨1, zero_lt_one, ?_⟩⟩
  intro t _
  erw [symmetric_truncation]
  simpa only [dist_self] using hη

/-- Moving the regular anchor does not alter divergence at the singularity. -/
private theorem negative_divergence (a : ℝ) (ha : a < 0) :
    E.rightDivergesNegValue (fun x => 1 / x) a (0 : WithTop ℝ) := by
  refine ⟨negative_regular a ha, fun B => ?_⟩
  let d := min (-a) (Real.exp (B + seriesLog (-a))) / 2
  have hd : 0 < d := half_pos (lt_min (neg_pos.mpr ha) (Real.exp_pos _))
  have hda : d < -a := by
    have := min_le_left (-a) (Real.exp (B + seriesLog (-a)))
    dsimp [d]; linarith
  have hde : d < Real.exp (B + seriesLog (-a)) := by
    have := min_le_right (-a) (Real.exp (B + seriesLog (-a)))
    dsimp [d]; linarith [Real.exp_pos (B + seriesLog (-a))]
  refine ⟨⟨-d, by constructor; linarith; exact WithTop.coe_lt_coe.mpr (neg_neg_of_pos hd)⟩, ?_⟩
  intro t ht
  have ht0 : t.val < 0 := WithTop.coe_lt_coe.mp t.property.2
  erw [negative_truncation a ha]
  have hlog : Real.log (-t.val) < B + seriesLog (-a) :=
    (Real.log_lt_iff_lt_exp (neg_pos.mpr ht0)).mpr (by dsimp at ht; linarith)
  rw [seriesLog_eq_realLog (-t.val) (neg_pos.mpr ht0)]
  linarith

private theorem positive_divergence (b : ℝ) (hb : 0 < b) :
    E.leftDivergesPosValue (fun x => 1 / x) (0 : WithBot ℝ) b := by
  refine ⟨positive_regular b hb, fun B => ?_⟩
  let d := min b (Real.exp (seriesLog b - B)) / 2
  have hd : 0 < d := half_pos (lt_min hb (Real.exp_pos _))
  have hdb : d < b := by
    have := min_le_left b (Real.exp (seriesLog b - B))
    dsimp [d]; linarith
  have hde : d < Real.exp (seriesLog b - B) := by
    have := min_le_right b (Real.exp (seriesLog b - B))
    dsimp [d]; linarith [Real.exp_pos (seriesLog b - B)]
  refine ⟨⟨d, WithBot.coe_lt_coe.mpr hd, hdb⟩, ?_⟩
  intro t ht
  have ht0 : 0 < t.val := WithBot.coe_lt_coe.mp t.property.1
  erw [positive_truncation b hb]
  have hlog : Real.log t.val < seriesLog b - B :=
    (Real.log_lt_iff_lt_exp ht0).mpr (lt_trans ht hde)
  rw [seriesLog_eq_realLog t.val ht0]
  linarith

theorem one_sided_divergence : oneSidedDivergence :=
  ⟨negative_divergence (-1) (by norm_num), positive_divergence 1 zero_lt_one⟩

theorem one_sided_nonconvergence : oneSidedNonconvergence := by
  exact ⟨Improper.right_infinite_not_converges _ _ _ (Or.inr one_sided_divergence.1),
    Improper.left_infinite_not_converges _ _ _ (Or.inl one_sided_divergence.2)⟩

theorem independent_nonconvergence : independentNonconvergence := by
  intro c h
  obtain ⟨L, v, hv, _⟩ := h
  obtain ⟨l, r, hl, hr, _⟩ := (hv (0 : Fin 2)).2
  have hc : (c (0 : Fin 2)).val < 0 :=
    WithTop.coe_lt_coe.mp (c (0 : Fin 2)).property.2
  exact Improper.right_infinite_not_converges _ _ _
    (Or.inr (negative_divergence _ hc)) ⟨r, hr⟩

end SingleVariableAnalysis.Riemann.PvCounterexample
