import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.PTest
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.OneEndpoint
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.MonotoneSubstitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.ElementaryPrimitives
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers

noncomputable section
namespace SingleVariableAnalysis.Riemann.Improper.PTest
open Set Filter
open scoped Topology BigOperators
open SingleVariableAnalysis
open SingleVariableAnalysis.Riemann

/-! Power and logarithmic tests for the shared proper Darboux and improper
integrals (paper.tex:3007–3033). The proper truncations are evaluated first;
only their explicit finite formulas are passed to endpoint limits. -/

/-- Newton–Leibniz for continuous derivative data, using the existing
Darboux/tagged bridge and the uniform cell error from proper substitution. -/
theorem integral_of_continuous_derivative {F f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) :
    ∃ h : RealIntegrable f a b, realIntegral f h = F b - F a := by
  have hc : C1OnInterval F f a b := ⟨hf, fun x hx => (hd x hx).hasDerivWithinAt⟩
  have hlim := fineTaggedLimit_of_image_sums (f := fun _ => (1 : ℝ)) hab hc
    ⟨1, by simp⟩ (I := F b - F a) (by
      intro ε hε
      refine ⟨1, zero_lt_one, fun P ξ _ => ?_⟩
      have he : imageTaggedSum P ξ F (fun _ => (1 : ℝ)) = F b - F a := by
        simpa only [imageTaggedSum, smul_eq_mul, mul_one, P.first, P.last] using
          sum_cell_differences (fun i => F (P.point i))
      simpa only [he, sub_self, norm_zero] using hε)
  have hb : BoundedOnInterval f a b :=
    ⟨isCompact_Icc.bddBelow_image hf, isCompact_Icc.bddAbove_image hf⟩
  apply (real_tagged_equivalence f hab hb _).mpr
  simpa only [smul_eq_mul, mul_one] using hlim


def primitive (p x : ℝ) : ℝ := if p = 1 then seriesLog x else realPower x (1-p) / (1-p)

theorem primitive_derivative (p x : ℝ) (hx : 0 < x) :
    HasDerivAt (primitive p) (realPower x (-p)) x := by
  by_cases hp : p = 1
  · subst p
    have he : realPower x (-1) = 1 / x := by
      rw [realPower_eq_rpow x hx]
      simp only [Real.rpow_neg_one, one_div]
    unfold primitive
    simp only [ite_true, he]
    exact seriesLog_hasDerivAt x hx
  · have hp' : -p ≠ -1 := by
      intro he
      apply hp
      linarith
    have h : HasDerivAt (fun t => realPower t (-p+1) / (-p+1))
        (realPower x (-p)) x := (ElementaryPrimitives.power_primitive (-p) hp').1 x hx
    rw [show -p+1 = 1-p by ring] at h
    unfold primitive
    simp only [ite_eq_right hp]
    exact h

theorem primitive_integral (p : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    ∃ h : RealIntegrable (fun x => realPower x (-p)) u v,
      realIntegral _ h = primitive p v - primitive p u := by
  exact integral_of_continuous_derivative huv.le
    ((realPower_continuous_base (-p)).mono (fun _ hx => hu.trans_le hx.1))
    (fun x hx => primitive_derivative p x (hu.trans_le hx.1))

theorem power_truncations : Specs.SingleVariableAnalysis.Ch10.PTest.powerTruncations := by
  intro p u v hu huv
  obtain ⟨h, hh⟩ := primitive_integral p hu huv
  refine ⟨h, hh.trans ?_⟩
  by_cases hp : p = 1 <;> simp [primitive, hp, sub_div] <;> rfl


/-- Convert an eventual assertion at infinity to a regular truncation cut. -/
theorem right_cut {a : ℝ} {P : ℝ → Prop} (h : ∀ᶠ x in atTop, P x) :
    ∃ r : RightIndex a ⊤, ∀ t : RightIndex a ⊤, r.val < t.val → P t.val := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp h
  refine ⟨⟨max a R + 1, (le_max_left _ _).trans_lt (lt_add_one _),
    WithTop.coe_lt_top _⟩, fun t ht => hR _ ?_⟩
  dsimp at ht
  linarith [le_max_right a R]

theorem left_cut {P : ℝ → Prop} (h : ∀ᶠ x in 𝓝[>] (0 : ℝ), P x) :
    ∃ r : LeftIndex (0 : WithBot ℝ) 1,
      ∀ t : LeftIndex (0 : WithBot ℝ) 1, t.val < r.val → P t.val := by
  obtain ⟨R, hR, hPR⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  have hm : 0 < min R 1 := lt_min hR zero_lt_one
  refine ⟨⟨min R 1 / 2, WithBot.coe_lt_coe.mpr (half_pos hm), ?_⟩, fun t ht => ?_⟩
  · have := min_le_right R 1
    linarith
  · apply hPR
    exact ⟨WithBot.coe_lt_coe.mp t.property.1,
      ht.trans (by dsimp; linarith [min_le_left R 1])⟩

theorem right_has_of_tendsto {f H : ℝ → ℝ} {a L : ℝ}
    (h : RightRegular .real f a ⊤)
    (he : ∀ t : RightIndex a ⊤, RightTruncation .real f a ⊤ h t = H t.val)
    (hL : Tendsto H atTop (𝓝 L)) : RightHasIntegral .real f a ⊤ L := by
  refine ⟨h, fun ε hε => ?_⟩
  obtain ⟨r, hr⟩ := right_cut (a := a) (hL.eventually (Metric.ball_mem_nhds L hε))
  refine ⟨r, fun t ht => ?_⟩
  change dist (RightTruncation .real f a ⊤ h t : ℝ) L < ε
  rw [he t]
  exact hr t ht

theorem right_diverges_of_tendsto {f H : ℝ → ℝ} {a : ℝ}
    (h : RightRegular .real f a ⊤)
    (he : ∀ t : RightIndex a ⊤, RightTruncation .real f a ⊤ h t = H t.val)
    (hL : Tendsto H atTop atTop) : RightDivergesPos f a ⊤ := by
  refine ⟨h, fun B => ?_⟩
  obtain ⟨r, hr⟩ := right_cut (a := a) (hL.eventually (eventually_gt_atTop B))
  refine ⟨r, fun t ht => ?_⟩
  change B < (RightTruncation .real f a ⊤ h t : ℝ)
  rw [he t]
  exact hr t ht

theorem left_has_of_tendsto {f H : ℝ → ℝ} {L : ℝ}
    (h : LeftRegular .real f (0 : WithBot ℝ) 1)
    (he : ∀ t : LeftIndex (0 : WithBot ℝ) 1,
      LeftTruncation .real f (0 : WithBot ℝ) 1 h t = H t.val)
    (hL : Tendsto H (𝓝[>] 0) (𝓝 L)) :
    LeftHasIntegral .real f (0 : WithBot ℝ) 1 L := by
  refine ⟨h, fun ε hε => ?_⟩
  obtain ⟨r, hr⟩ := left_cut (hL.eventually (Metric.ball_mem_nhds L hε))
  refine ⟨r, fun t ht => ?_⟩
  change dist (LeftTruncation .real f (0 : WithBot ℝ) 1 h t : ℝ) L < ε
  rw [he t]
  exact hr t ht

theorem left_diverges_of_tendsto {f H : ℝ → ℝ}
    (h : LeftRegular .real f (0 : WithBot ℝ) 1)
    (he : ∀ t : LeftIndex (0 : WithBot ℝ) 1,
      LeftTruncation .real f (0 : WithBot ℝ) 1 h t = H t.val)
    (hL : Tendsto H (𝓝[>] 0) atTop) : LeftDivergesPos f (0 : WithBot ℝ) 1 := by
  refine ⟨h, fun B => ?_⟩
  obtain ⟨r, hr⟩ := left_cut (hL.eventually (eventually_gt_atTop B))
  refine ⟨r, fun t ht => ?_⟩
  change B < (LeftTruncation .real f (0 : WithBot ℝ) 1 h t : ℝ)
  rw [he t]
  exact hr t ht

theorem power_right_regular (p a : ℝ) (ha : 0 < a) :
    RightRegular .real (fun x => realPower x (-p)) a ⊤ :=
  ⟨WithTop.coe_lt_top _, fun t => (primitive_integral p ha t.property.1).choose⟩

theorem power_left_regular (p : ℝ) :
    LeftRegular .real (fun x => realPower x (-p)) (0 : WithBot ℝ) 1 :=
  ⟨WithBot.coe_lt_coe.mpr zero_lt_one, fun t =>
    (primitive_integral p (WithBot.coe_lt_coe.mp t.property.1) t.property.2).choose⟩

theorem power_right_formula (p a : ℝ) (ha : 0 < a) (t : RightIndex a ⊤) :
    RightTruncation .real (fun x => realPower x (-p)) a ⊤ (power_right_regular p a ha) t =
      primitive p t.val - primitive p a :=
  (primitive_integral p ha t.property.1).choose_spec

theorem power_left_formula (p : ℝ) (t : LeftIndex (0 : WithBot ℝ) 1) :
    LeftTruncation .real (fun x => realPower x (-p)) (0 : WithBot ℝ) 1
      (power_left_regular p) t = primitive p 1 - primitive p t.val :=
  (primitive_integral p (WithBot.coe_lt_coe.mp t.property.1) t.property.2).choose_spec

theorem primitive_atTop_zero (p : ℝ) (hp : 1 < p) :
    Tendsto (primitive p) atTop (𝓝 0) := by
  have hn : p ≠ 1 := ne_of_gt hp
  unfold primitive
  simpa only [ite_eq_right hn, zero_div] using
    (realPower_neg_tendsto_atTop (1-p) (by linarith)).div_const (1-p)

theorem primitive_atTop_infinite (p : ℝ) (hp : p ≤ 1) :
    Tendsto (primitive p) atTop atTop := by
  rcases hp.eq_or_lt with rfl | hp
  · unfold primitive
    simp only [ite_true]
    exact seriesLog_tendsto_atTop
  · have hn : p ≠ 1 := ne_of_lt hp
    unfold primitive
    simpa only [ite_eq_right hn] using
      (realPower_pos_tendsto_atTop (1-p) (by linarith)).atTop_div_const (by linarith : 0 < 1-p)

theorem primitive_zero_finite (p : ℝ) (hp : p < 1) :
    Tendsto (primitive p) (𝓝[>] 0) (𝓝 0) := by
  have hn : p ≠ 1 := ne_of_lt hp
  unfold primitive
  simpa only [ite_eq_right hn, zero_div] using
    (realPower_pos_tendsto_zero_right (1-p) (by linarith)).div_const (1-p)

theorem primitive_zero_infinite (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (primitive p) (𝓝[>] 0) atBot := by
  rcases hp.eq_or_lt with rfl | hp
  · unfold primitive
    simp only [ite_true]
    exact seriesLog_tendsto_zero_right
  · have hn : p ≠ 1 := ne_of_gt hp
    unfold primitive
    simpa only [ite_eq_right hn] using
      (realPower_neg_tendsto_zero_right (1-p) (by linarith)).atTop_div_const_of_neg
        (by linarith : 1-p < 0)

theorem primitive_one (p : ℝ) (hp : p ≠ 1) : primitive p 1 = 1 / (1-p) := by
  simp only [primitive, ite_eq_right hp]
  rw [realPower_eq_rpow 1 zero_lt_one, Real.one_rpow]

theorem power_infinity_value : Specs.SingleVariableAnalysis.Ch10.PTest.powerInfinityValue := by
  intro p hp
  apply right_has_of_tendsto (H := fun x => primitive p x - primitive p 1)
    (power_right_regular p 1 zero_lt_one)
    (power_right_formula p 1 zero_lt_one)
  have h := (primitive_atTop_zero p hp).sub_const (primitive p 1)
  have he : 0 - primitive p 1 = 1 / (p-1) := by
    rw [primitive_one p (ne_of_gt hp), zero_sub, show 1-p = -(p-1) by ring]
    simp only [one_div, inv_neg, neg_neg]
  rw [he] at h
  exact h

theorem power_infinity_divergence :
    Specs.SingleVariableAnalysis.Ch10.PTest.powerInfinityDivergence := by
  intro p hp
  apply right_diverges_of_tendsto (H := fun x => primitive p x - primitive p 1)
    (power_right_regular p 1 zero_lt_one)
    (power_right_formula p 1 zero_lt_one)
  simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop
    (-primitive p 1) (primitive_atTop_infinite p hp)

theorem power_infinity_iff : Specs.SingleVariableAnalysis.Ch10.PTest.powerInfinityIff := by
  intro p
  constructor
  · intro h
    by_contra hp
    exact right_infinite_not_converges _ _ _
      (Or.inl (power_infinity_divergence p (le_of_not_gt hp))) h
  · intro hp
    exact ⟨_, power_infinity_value p hp⟩

theorem power_zero_value : Specs.SingleVariableAnalysis.Ch10.PTest.powerZeroValue := by
  intro p hp
  apply left_has_of_tendsto (H := fun x => primitive p 1 - primitive p x)
    (power_left_regular p) (power_left_formula p)
  have h := (primitive_zero_finite p hp).const_sub (primitive p 1)
  simp only [primitive_one p (ne_of_lt hp), sub_zero] at h ⊢
  exact h

theorem power_zero_divergence : Specs.SingleVariableAnalysis.Ch10.PTest.powerZeroDivergence := by
  intro p hp
  apply left_diverges_of_tendsto (H := fun x => primitive p 1 - primitive p x)
    (power_left_regular p) (power_left_formula p)
  simpa only [sub_eq_add_neg, Function.comp_apply] using tendsto_atTop_add_const_left (𝓝[>] (0 : ℝ))
    (primitive p 1) (tendsto_neg_atBot_atTop.comp (primitive_zero_infinite p hp))

theorem power_zero_iff : Specs.SingleVariableAnalysis.Ch10.PTest.powerZeroIff := by
  intro p
  constructor
  · intro h
    by_contra hp
    exact left_infinite_not_converges _ _ _
      (Or.inl (power_zero_divergence p (le_of_not_gt hp))) h
  · intro hp
    exact ⟨_, power_zero_value p hp⟩

theorem log_positive {x : ℝ} (hx : 1 < x) : 0 < seriesLog x := by
  rw [seriesLog_eq_realLog x (zero_lt_one.trans hx)]
  exact Real.log_pos hx

theorem logarithmic_derivative (q x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t => primitive q (seriesLog t))
      (1 / (x * realPower (seriesLog x) q)) x := by
  have h := (primitive_derivative q (seriesLog x) (log_positive hx)).comp x
    (seriesLog_hasDerivAt x (zero_lt_one.trans hx))
  convert h using 1
  · rfl
  rw [realPower_eq_rpow _ (log_positive hx),
    realPower_eq_rpow _ (log_positive hx), Real.rpow_neg (log_positive hx).le]
  simp only [one_div, mul_inv_rev]

theorem logarithmic_integral (q : ℝ) {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    ∃ h : RealIntegrable (fun x => 1 / (x * realPower (seriesLog x) q)) a b,
      realIntegral _ h = primitive q (seriesLog b) - primitive q (seriesLog a) := by
  have hx (x : ℝ) (hx : x ∈ Icc a b) : 1 < x := ha.trans_le hx.1
  have hcLog : ContinuousOn seriesLog (Icc a b) := fun x h =>
    (seriesLog_hasDerivAt x (zero_lt_one.trans (hx x h))).continuousAt.continuousWithinAt
  have hcPow : ContinuousOn (fun x => realPower (seriesLog x) q) (Icc a b) :=
    (realPower_continuous_base q).comp hcLog (fun x h => log_positive (hx x h))
  apply integral_of_continuous_derivative hab.le
    (continuousOn_const.div (continuousOn_id.mul hcPow) ?_)
    (fun x h => logarithmic_derivative q x (hx x h))
  intro x h
  exact (mul_pos (zero_lt_one.trans (hx x h))
    (realPower_pos _ (log_positive (hx x h)) q)).ne'

theorem logarithmic_regular (q A : ℝ) (hA : 1 < A) :
    RightRegular .real (fun x => 1 / (x * realPower (seriesLog x) q)) A ⊤ :=
  ⟨WithTop.coe_lt_top _, fun t => (logarithmic_integral q hA t.property.1).choose⟩

theorem logarithmic_formula (q A : ℝ) (hA : 1 < A) (t : RightIndex A ⊤) :
    RightTruncation .real (fun x => 1 / (x * realPower (seriesLog x) q)) A ⊤
      (logarithmic_regular q A hA) t = primitive q (seriesLog t.val) - primitive q (seriesLog A) :=
  (logarithmic_integral q hA t.property.1).choose_spec

theorem logarithmic_hasIntegral (q A : ℝ) (hA : 1 < A) (hq : 1 < q) :
    RightHasIntegral .real (fun x => 1 / (x * realPower (seriesLog x) q)) A ⊤
      (-primitive q (seriesLog A)) := by
  apply right_has_of_tendsto (H := fun x => primitive q (seriesLog x) - primitive q (seriesLog A))
    (logarithmic_regular q A hA) (logarithmic_formula q A hA)
  simpa only [zero_sub, Function.comp_apply] using
    ((primitive_atTop_zero q hq).comp (show Tendsto seriesLog atTop atTop from seriesLog_tendsto_atTop)).sub_const (primitive q (seriesLog A))

theorem logarithmic_divergence (q A : ℝ) (hA : 1 < A) (hq : q ≤ 1) :
    RightDivergesPos (fun x => 1 / (x * realPower (seriesLog x) q)) A ⊤ := by
  apply right_diverges_of_tendsto (H := fun x => primitive q (seriesLog x) - primitive q (seriesLog A))
    (logarithmic_regular q A hA) (logarithmic_formula q A hA)
  simpa only [sub_eq_add_neg, Function.comp_apply] using tendsto_atTop_add_const_right atTop
    (-primitive q (seriesLog A)) ((primitive_atTop_infinite q hq).comp (show Tendsto seriesLog atTop atTop from seriesLog_tendsto_atTop))

theorem logarithmic_iff : Specs.SingleVariableAnalysis.Ch10.PTest.logarithmicIff := by
  intro A hA q
  constructor
  · intro h
    by_contra hq
    exact right_infinite_not_converges _ _ _
      (Or.inl (logarithmic_divergence q A hA (le_of_not_gt hq))) h
  · intro hq
    exact ⟨_, logarithmic_hasIntegral q A hA hq⟩

end SingleVariableAnalysis.Riemann.Improper.PTest
