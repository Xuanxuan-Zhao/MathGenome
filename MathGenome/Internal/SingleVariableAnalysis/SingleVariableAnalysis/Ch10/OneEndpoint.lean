import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Oriented
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OneEndpoint

/-! Improper integrals are finite limits of proper Darboux truncations.
The auxiliary functions have subtype domains: every value carries a proof of
proper integrability. In particular no default integral is used outside that domain.
-/
namespace SingleVariableAnalysis.Riemann.Improper
namespace E
export Specs.SingleVariableAnalysis.Ch10.OneEndpoint
  (rightIndexValue leftIndexValue rightRegularValue
   leftRegularValue rightTruncationValue leftTruncationValue
   rightHasIntegralValue rightConvergesValue rightIntegralValue
   rightReverseHasIntegralValue rightReverseIntegralValue rightDivergesPosValue
   rightDivergesNegValue rightNormDivergesValue leftHasIntegralValue
   leftConvergesValue leftIntegralValue leftReverseHasIntegralValue
   leftReverseIntegralValue leftDivergesPosValue leftDivergesNegValue
   leftNormDivergesValue)
end E
noncomputable abbrev RightIndex := @E.rightIndexValue
noncomputable abbrev LeftIndex := @E.leftIndexValue
noncomputable abbrev RightRegular := @E.rightRegularValue
noncomputable abbrev LeftRegular := @E.leftRegularValue
noncomputable abbrev RightTruncation := @E.rightTruncationValue
noncomputable abbrev LeftTruncation := @E.leftTruncationValue
noncomputable abbrev RightHasIntegral := @E.rightHasIntegralValue
noncomputable abbrev RightConverges := @E.rightConvergesValue
noncomputable abbrev RightIntegral := @E.rightIntegralValue
noncomputable abbrev RightReverseHasIntegral := @E.rightReverseHasIntegralValue
noncomputable abbrev RightReverseIntegral := @E.rightReverseIntegralValue
noncomputable abbrev RightDivergesPos := @E.rightDivergesPosValue
noncomputable abbrev RightDivergesNeg := @E.rightDivergesNegValue
noncomputable abbrev RightNormDiverges := @E.rightNormDivergesValue
noncomputable abbrev LeftHasIntegral := @E.leftHasIntegralValue
noncomputable abbrev LeftConverges := @E.leftConvergesValue
noncomputable abbrev LeftIntegral := @E.leftIntegralValue
noncomputable abbrev LeftReverseHasIntegral := @E.leftReverseHasIntegralValue
noncomputable abbrev LeftReverseIntegral := @E.leftReverseIntegralValue
noncomputable abbrev LeftDivergesPos := @E.leftDivergesPosValue
noncomputable abbrev LeftDivergesNeg := @E.leftDivergesNegValue
noncomputable abbrev LeftNormDiverges := @E.leftNormDivergesValue

open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open SingleVariableAnalysis

/-- There is always a regular truncation beyond any two given ones. -/
theorem right_later {a : ℝ} {b : WithTop ℝ} (r s : RightIndex a b) :
    ∃ t : RightIndex a b, r.val < t.val ∧ s.val < t.val := by
  cases b using WithTop.recTopCoe with
  | top =>
    refine ⟨⟨max r.val s.val + 1, ?_, ?_⟩, ?_, ?_⟩
    · exact r.property.1.trans ((le_max_left r.val s.val).trans_lt (lt_add_one _))
    · exact WithTop.coe_lt_top _
    · exact (le_max_left r.val s.val).trans_lt (lt_add_one _)
    · exact (le_max_right r.val s.val).trans_lt (lt_add_one _)
  | coe b =>
    have hr : r.val < b := WithTop.coe_lt_coe.mp r.property.2
    have hs : s.val < b := WithTop.coe_lt_coe.mp s.property.2
    obtain ⟨t, ht, htb⟩ := exists_between (max_lt hr hs)
    exact ⟨⟨t, r.property.1.trans ((le_max_left _ _).trans_lt ht),
      WithTop.coe_lt_coe.mpr htb⟩,
      (le_max_left _ _).trans_lt ht, (le_max_right _ _).trans_lt ht⟩

theorem left_earlier {a : WithBot ℝ} {b : ℝ} (r s : LeftIndex a b) :
    ∃ t : LeftIndex a b, t.val < r.val ∧ t.val < s.val := by
  cases a using WithBot.recBotCoe with
  | bot =>
    refine ⟨⟨min r.val s.val - 1, ?_, ?_⟩, ?_, ?_⟩
    · exact WithBot.bot_lt_coe _
    · exact lt_trans (sub_one_lt _) ((min_le_left _ _).trans_lt r.property.2)
    · exact lt_of_lt_of_le (sub_one_lt _) (min_le_left _ _)
    · exact lt_of_lt_of_le (sub_one_lt _) (min_le_right _ _)
  | coe a =>
    have hr : a < r.val := WithBot.coe_lt_coe.mp r.property.1
    have hs : a < s.val := WithBot.coe_lt_coe.mp s.property.1
    obtain ⟨t, hat, ht⟩ := exists_between (lt_min hr hs)
    exact ⟨⟨t, WithBot.coe_lt_coe.mpr hat,
      (ht.trans_le (min_le_left _ _)).trans r.property.2⟩,
      ht.trans_le (min_le_left _ _), ht.trans_le (min_le_right _ _)⟩

theorem right_unique : rightUnique := by
  intro k f a b L M hL hM
  rcases hL with ⟨h, hL⟩
  rcases hM with ⟨h', hM⟩
  apply eq_of_dist_eq_zero
  apply le_antisymm _ dist_nonneg
  by_contra hn
  have hd : 0 < dist L M := lt_of_not_ge hn
  obtain ⟨r, hr⟩ := hL (dist L M / 2) (half_pos hd)
  obtain ⟨s, hs⟩ := hM (dist L M / 2) (half_pos hd)
  obtain ⟨t, hrt, hst⟩ := right_later r s
  have h1 := hr t hrt
  have h2 := hs t hst
  have htri := dist_triangle_left L M (RightTruncation k f a b h t)
  linarith

theorem left_unique : leftUnique := by
  intro k f a b L M hL hM
  rcases hL with ⟨h, hL⟩
  rcases hM with ⟨h', hM⟩
  apply eq_of_dist_eq_zero
  apply le_antisymm _ dist_nonneg
  by_contra hn
  have hd : 0 < dist L M := lt_of_not_ge hn
  obtain ⟨r, hr⟩ := hL (dist L M / 2) (half_pos hd)
  obtain ⟨s, hs⟩ := hM (dist L M / 2) (half_pos hd)
  obtain ⟨t, hrt, hst⟩ := left_earlier r s
  have h1 := hr t hrt
  have h2 := hs t hst
  have htri := dist_triangle_left L M (LeftTruncation k f a b h t)
  linarith

theorem right_integral_hasValue : rightIntegralHasValue := by
  intro k f a b h
  exact Classical.choose_spec h

theorem left_integral_hasValue : leftIntegralHasValue := by
  intro k f a b h
  exact Classical.choose_spec h

theorem right_integral_eq : rightIntegralEq := by
  intro k f a b h L hL
  exact right_unique k f a b _ L (right_integral_hasValue k f a b h) hL

theorem left_integral_eq : leftIntegralEq := by
  intro k f a b h L hL
  exact left_unique k f a b _ L (left_integral_hasValue k f a b h) hL

theorem right_reverse_hasValue : rightReverseHasValue := by
  intro k f a b h
  change RightHasIntegral k f a b (- -RightIntegral k f a b h)
  rw [neg_neg]
  exact right_integral_hasValue k f a b h

theorem left_reverse_hasValue : leftReverseHasValue := by
  intro k f a b h
  change LeftHasIntegral k f a b (- -LeftIntegral k f a b h)
  rw [neg_neg]
  exact left_integral_hasValue k f a b h

private theorem left_accumulation_Ioo {a b : ℝ} (hab : a < b) :
    LeftAccumulation (Set.Ioo a b) b := by
  intro δ hδ
  have hm : max a (b - δ) < b := max_lt hab (by linarith)
  obtain ⟨t, ht, htb⟩ := exists_between hm
  exact ⟨t, ⟨(le_max_left _ _).trans_lt ht, htb⟩,
    (le_max_right _ _).trans_lt ht, htb⟩

private theorem right_accumulation_Ioo {a b : ℝ} (hab : a < b) :
    RightAccumulation (Set.Ioo a b) a := by
  intro δ hδ
  have hm : a < min b (a + δ) := lt_min hab (by linarith)
  obtain ⟨t, hat, ht⟩ := exists_between hm
  exact ⟨t, ⟨hat, ht.trans_le (min_le_left _ _)⟩,
    hat, ht.trans_le (min_le_right _ _)⟩

theorem right_finite_limit_iff : rightFiniteLimitIff := by
  intro k f a b h H hext L
  change RightHasIntegral k f a (b : WithTop ℝ) L ↔ LeftRelativeLimit H (Set.Ioo a b) b L
  rw [leftRelativeLimit_iff]
  have hab : a < b := WithTop.coe_lt_coe.mp h.1
  have hacc := left_accumulation_Ioo hab
  constructor
  · rintro ⟨h', hL⟩
    refine ⟨hacc, fun ε hε => ?_⟩
    obtain ⟨r, hr⟩ := hL ε hε
    have hrb : r.val < b := WithTop.coe_lt_coe.mp r.property.2
    refine ⟨b - r.val, sub_pos.mpr hrb, fun t ht hrt _ => ?_⟩
    let ti : RightIndex a (b : WithTop ℝ) := ⟨t, ht.1, WithTop.coe_lt_coe.mpr ht.2⟩
    rw [hext ti]
    exact hr ti (by dsimp [ti]; linarith)
  · rintro ⟨_, hL⟩
    refine ⟨h, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδL⟩ := hL ε hε
    obtain ⟨r, hr, hrδ⟩ := hacc δ hδ
    refine ⟨⟨r, hr.1, WithTop.coe_lt_coe.mpr hr.2⟩, fun t hrt => ?_⟩
    rw [← hext t]
    exact hδL t.val ⟨t.property.1, WithTop.coe_lt_coe.mp t.property.2⟩
      (by dsimp at hrt; linarith [hrδ.1]) (WithTop.coe_lt_coe.mp t.property.2)

theorem left_finite_limit_iff : leftFiniteLimitIff := by
  intro k f a b h H hext L
  change LeftHasIntegral k f (a : WithBot ℝ) b L ↔ RightRelativeLimit H (Set.Ioo a b) a L
  rw [rightRelativeLimit_iff]
  have hab : a < b := WithBot.coe_lt_coe.mp h.1
  have hacc := right_accumulation_Ioo hab
  constructor
  · rintro ⟨h', hL⟩
    refine ⟨hacc, fun ε hε => ?_⟩
    obtain ⟨r, hr⟩ := hL ε hε
    have har : a < r.val := WithBot.coe_lt_coe.mp r.property.1
    refine ⟨r.val - a, sub_pos.mpr har, fun t ht _ htr => ?_⟩
    let ti : LeftIndex (a : WithBot ℝ) b := ⟨t, WithBot.coe_lt_coe.mpr ht.1, ht.2⟩
    rw [hext ti]
    exact hr ti (by dsimp [ti]; linarith)
  · rintro ⟨_, hL⟩
    refine ⟨h, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδL⟩ := hL ε hε
    obtain ⟨r, hr, hrδ⟩ := hacc δ hδ
    refine ⟨⟨r, WithBot.coe_lt_coe.mpr hr.1, hr.2⟩, fun t htr => ?_⟩
    rw [← hext t]
    exact hδL t.val ⟨WithBot.coe_lt_coe.mp t.property.1, t.property.2⟩
      (WithBot.coe_lt_coe.mp t.property.1) (by dsimp at htr; linarith [hrδ.2])

theorem right_infinite_limit_iff : rightInfiniteLimitIff := by
  intro k f a h H hext L
  change RightHasIntegral k f a ⊤ L ↔ LimitAtPosInfinity H (Set.Ioi a) L
  rw [limitAtPosInfinity_iff]
  constructor
  · rintro ⟨h', hL⟩
    constructor
    · intro A _
      exact ⟨max a A + 1, (show a < max a A + 1 from (le_max_left a A).trans_lt (lt_add_one _)),
        (show A < max a A + 1 from (le_max_right a A).trans_lt (lt_add_one _))⟩
    · intro ε hε
      obtain ⟨r, hr⟩ := hL ε hε
      refine ⟨max r.val 0 + 1, by linarith [le_max_right r.val 0], fun t ht hrt => ?_⟩
      let ti : RightIndex a ⊤ := ⟨t, ht, WithTop.coe_lt_top _⟩
      rw [hext ti]
      exact hr ti (by dsimp [ti]; linarith [le_max_left r.val 0])
  · rintro ⟨_, hL⟩
    refine ⟨h, fun ε hε => ?_⟩
    obtain ⟨A, _, hA⟩ := hL ε hε
    refine ⟨⟨max a A + 1, (le_max_left _ _).trans_lt (lt_add_one _),
      WithTop.coe_lt_top _⟩, fun t hrt => ?_⟩
    rw [← hext t]
    exact hA t.val t.property.1 (by dsimp at hrt; linarith [le_max_right a A])

theorem left_infinite_limit_iff : leftInfiniteLimitIff := by
  intro k f b h H hext L
  change LeftHasIntegral k f ⊥ b L ↔ LimitAtNegInfinity H (Set.Iio b) L
  rw [limitAtNegInfinity_iff]
  constructor
  · rintro ⟨h', hL⟩
    constructor
    · intro A _
      exact ⟨min b (-A) - 1, (show min b (-A) - 1 < b from (sub_one_lt _).trans_le (min_le_left b (-A))),
        (show min b (-A) - 1 < -A from (sub_one_lt _).trans_le (min_le_right b (-A)))⟩
    · intro ε hε
      obtain ⟨r, hr⟩ := hL ε hε
      refine ⟨max (-r.val) 0 + 1, by linarith [le_max_right (-r.val) 0], fun t ht htr => ?_⟩
      let ti : LeftIndex ⊥ b := ⟨t, WithBot.bot_lt_coe _, ht⟩
      rw [hext ti]
      exact hr ti (by dsimp [ti]; linarith [le_max_left (-r.val) 0])
  · rintro ⟨_, hL⟩
    refine ⟨h, fun ε hε => ?_⟩
    obtain ⟨A, _, hA⟩ := hL ε hε
    refine ⟨⟨min b (-A) - 1, WithBot.bot_lt_coe _,
      (sub_one_lt _).trans_le (min_le_left _ _)⟩, fun t htr => ?_⟩
    rw [← hext t]
    exact hA t.val t.property.2 (by dsimp at htr; linarith [min_le_right b (-A)])

theorem right_normInfinite_not_converges : rightNormInfiniteNotConverges := by
  intro k f a b hd hc
  rcases hd with ⟨h, hd⟩
  rcases hc with ⟨L, h', hL⟩
  obtain ⟨r, hr⟩ := hd (‖L‖ + 1)
  obtain ⟨s, hs⟩ := hL 1 zero_lt_one
  obtain ⟨t, hrt, hst⟩ := right_later r s
  have hd' := hr t hrt
  have hc' := hs t hst
  have hb : ‖RightTruncation k f a b h t‖ ≤ ‖L‖ + 1 :=
    norm_le_norm_add_const_of_dist_le hc'.le
  linarith

theorem left_normInfinite_not_converges : leftNormInfiniteNotConverges := by
  intro k f a b hd hc
  rcases hd with ⟨h, hd⟩
  rcases hc with ⟨L, h', hL⟩
  obtain ⟨r, hr⟩ := hd (‖L‖ + 1)
  obtain ⟨s, hs⟩ := hL 1 zero_lt_one
  obtain ⟨t, hrt, hst⟩ := left_earlier r s
  have hd' := hr t hrt
  have hc' := hs t hst
  have hb : ‖LeftTruncation k f a b h t‖ ≤ ‖L‖ + 1 :=
    norm_le_norm_add_const_of_dist_le hc'.le
  linarith

theorem right_infinite_not_converges : rightInfiniteNotConverges := by
  intro f a b hd
  apply right_normInfinite_not_converges .real f a b
  rcases hd with ⟨h, hd⟩ | ⟨h, hd⟩
  · refine ⟨h, fun B => ?_⟩
    obtain ⟨r, hr⟩ := hd B
    refine ⟨r, fun t ht => ?_⟩
    change B < |(show ℝ from RightTruncation .real f a b h t)|
    exact (hr t ht).trans_le (le_abs_self _)
  · refine ⟨h, fun B => ?_⟩
    obtain ⟨r, hr⟩ := hd (-B)
    refine ⟨r, fun t ht => ?_⟩
    change B < |(show ℝ from RightTruncation .real f a b h t)|
    have hx := hr t ht
    have hb := neg_le_abs (show ℝ from RightTruncation .real f a b h t)
    linarith

theorem left_infinite_not_converges : leftInfiniteNotConverges := by
  intro f a b hd
  apply left_normInfinite_not_converges .real f a b
  rcases hd with ⟨h, hd⟩ | ⟨h, hd⟩
  · refine ⟨h, fun B => ?_⟩
    obtain ⟨r, hr⟩ := hd B
    refine ⟨r, fun t ht => ?_⟩
    change B < |(show ℝ from LeftTruncation .real f a b h t)|
    exact (hr t ht).trans_le (le_abs_self _)
  · refine ⟨h, fun B => ?_⟩
    obtain ⟨r, hr⟩ := hd (-B)
    refine ⟨r, fun t ht => ?_⟩
    change B < |(show ℝ from LeftTruncation .real f a b h t)|
    have hx := hr t ht
    have hb := neg_le_abs (show ℝ from LeftTruncation .real f a b h t)
    linarith


theorem right_real_orientation : rightRealOrientation := by
  intro f a b h t
  have huv : a ≤ t.val := t.property.1.le
  have hf : RealIntegrable f a t.val := h.2 t
  have ho : OrientedRealIntegrable f t.val a := by
    simpa [OrientedRealIntegrable, O.realIntegrableValue,
      min_eq_right huv, max_eq_left huv] using hf
  have hp : OrientedRealIntegrable f a t.val := by
    simpa [OrientedRealIntegrable, O.realIntegrableValue,
      min_eq_left huv, max_eq_right huv] using hf
  refine ⟨ho, ?_⟩
  rw [oriented_real_symmetry f t.val a ho hp,
    oriented_real_agreement f huv hp hf]
  rfl

theorem right_complex_orientation : rightComplexOrientation := by
  intro f a b h t
  have huv : a ≤ t.val := t.property.1.le
  have hf : ComplexIntegrable f a t.val := h.2 t
  have ho : OrientedComplexIntegrable f t.val a := by
    simpa [OrientedComplexIntegrable, O.complexIntegrableValue,
      min_eq_right huv, max_eq_left huv] using hf
  have hp : OrientedComplexIntegrable f a t.val := by
    simpa [OrientedComplexIntegrable, O.complexIntegrableValue,
      min_eq_left huv, max_eq_right huv] using hf
  refine ⟨ho, ?_⟩
  rw [oriented_complex_symmetry f t.val a ho hp,
    oriented_complex_agreement f huv hp hf]
  rfl

theorem right_reverse_converges_iff : rightReverseConvergesIff := by
  intro k f a b
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨-L, hL⟩
  · rintro ⟨L, hL⟩
    refine ⟨-L, ?_⟩
    change RightHasIntegral k f a b (- -L)
    simpa only [neg_neg] using hL

theorem left_real_orientation : leftRealOrientation := by
  intro f a b h t
  have huv : t.val ≤ b := t.property.2.le
  have hf : RealIntegrable f t.val b := h.2 t
  have ho : OrientedRealIntegrable f b t.val := by
    simpa [OrientedRealIntegrable, O.realIntegrableValue,
      min_eq_right huv, max_eq_left huv] using hf
  have hp : OrientedRealIntegrable f t.val b := by
    simpa [OrientedRealIntegrable, O.realIntegrableValue,
      min_eq_left huv, max_eq_right huv] using hf
  refine ⟨ho, ?_⟩
  rw [oriented_real_symmetry f b t.val ho hp,
    oriented_real_agreement f huv hp hf]
  rfl

theorem left_complex_orientation : leftComplexOrientation := by
  intro f a b h t
  have huv : t.val ≤ b := t.property.2.le
  have hf : ComplexIntegrable f t.val b := h.2 t
  have ho : OrientedComplexIntegrable f b t.val := by
    simpa [OrientedComplexIntegrable, O.complexIntegrableValue,
      min_eq_right huv, max_eq_left huv] using hf
  have hp : OrientedComplexIntegrable f t.val b := by
    simpa [OrientedComplexIntegrable, O.complexIntegrableValue,
      min_eq_left huv, max_eq_right huv] using hf
  refine ⟨ho, ?_⟩
  rw [oriented_complex_symmetry f b t.val ho hp,
    oriented_complex_agreement f huv hp hf]
  rfl

theorem left_reverse_converges_iff : leftReverseConvergesIff := by
  intro k f a b
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨-L, hL⟩
  · rintro ⟨L, hL⟩
    refine ⟨-L, ?_⟩
    change LeftHasIntegral k f a b (- -L)
    simpa only [neg_neg] using hL

end SingleVariableAnalysis.Riemann.Improper
