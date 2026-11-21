import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.SeveralEndpoints
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Algebra
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.PrincipalValue

namespace SingleVariableAnalysis.Riemann.PrincipalValue
open Specs.SingleVariableAnalysis.Ch10.PrincipalValue
open SingleVariableAnalysis

abbrev InteriorIndex := interiorIndexValue
abbrev InteriorRegular := interiorRegularValue
noncomputable abbrev interiorTruncation := interiorTruncationValue
noncomputable abbrev InteriorHasIntegral := interiorHasIntegralValue
noncomputable abbrev InteriorConverges := interiorConvergesValue
noncomputable abbrev interiorIntegral := interiorIntegralValue
noncomputable abbrev ControlledInteriorHasIntegral := controlledInteriorHasIntegralValue
noncomputable abbrev ControlledInteriorConverges := controlledInteriorConvergesValue
noncomputable abbrev controlledInteriorIntegral := controlledInteriorIntegralValue
noncomputable abbrev CoreHasIntegral := coreHasIntegralValue
abbrev WholeLineIndex := wholeLineIndexValue
abbrev WholeLineRegular := wholeLineRegularValue
noncomputable abbrev wholeLineTruncation := wholeLineTruncationValue
noncomputable abbrev WholeLineHasIntegral := wholeLineHasIntegralValue
noncomputable abbrev WholeLineConverges := wholeLineConvergesValue
noncomputable abbrev wholeLineIntegral := wholeLineIntegralValue

/-- The symmetric punctured intervals have arbitrarily small positive radii. -/
private theorem interior_small {a b c δ : ℝ} (ha : a < c) (hb : c < b) (hδ : 0 < δ) :
    ∃ t : InteriorIndex a b c, t.val < δ := by
  let d := min δ (min (c-a) (b-c))
  have hd : 0 < d := lt_min hδ (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))
  have h1 : d ≤ δ := min_le_left _ _
  have h2 : d ≤ c-a := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : d ≤ b-c := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨⟨d/2, by constructor; linarith; constructor <;> linarith⟩, by dsimp; linarith⟩

theorem interior_unique : interiorUnique := by
  intro k f a b c L M hL hM
  rcases hL with ⟨h, hL⟩
  rcases hM with ⟨h', hM⟩
  apply eq_of_dist_eq_zero
  apply le_antisymm _ dist_nonneg
  by_contra hn
  have hd : 0 < dist L M := lt_of_not_ge hn
  obtain ⟨δ, hδ, hδL⟩ := hL (dist L M/2) (half_pos hd)
  obtain ⟨ρ, hρ, hρM⟩ := hM (dist L M/2) (half_pos hd)
  obtain ⟨t, ht⟩ := interior_small (WithTop.coe_lt_coe.mp h.1.1)
    (WithBot.coe_lt_coe.mp h.2.1) (lt_min hδ hρ)
  have h1 := hδL t (ht.trans_le (min_le_left _ _))
  have h2 := hρM t (ht.trans_le (min_le_right _ _))
  have htri := dist_triangle_left L M (interiorTruncation k f a b c h t)
  linarith

theorem interior_integral_hasValue : interiorIntegralHasValue := by
  intro k f a b c h
  exact Classical.choose_spec h

theorem interior_integral_eq : interiorIntegralEq := by
  intro k f a b c h L hL
  exact interior_unique k f a b c _ L (interior_integral_hasValue k f a b c h) hL

/-- The two independent cutoff estimates are restricted to the single linked
rule ε ↦ (c-ε,c+ε). Their errors each contribute less than half the tolerance. -/
theorem interior_of_independent : interiorOfIndependent := by
  intro k f a b c l r hl hr
  rcases hl with ⟨hlreg, hl⟩
  rcases hr with ⟨hrreg, hr⟩
  let h : InteriorRegular k f a b c := ⟨hlreg, hrreg⟩
  refine ⟨h, fun η hη => ?_⟩
  obtain ⟨s, hs⟩ := hl (η/2) (half_pos hη)
  obtain ⟨t, ht⟩ := hr (η/2) (half_pos hη)
  have hsc : s.val < c := WithTop.coe_lt_coe.mp s.property.2
  have hct : c < t.val := WithBot.coe_lt_coe.mp t.property.1
  refine ⟨min (c-s.val) (t.val-c), lt_min (sub_pos.mpr hsc) (sub_pos.mpr hct), ?_⟩
  intro e he
  let si : E.rightIndexValue a (c : WithTop ℝ) :=
    ⟨c-e.val, e.property.2.1, WithTop.coe_lt_coe.mpr (by linarith [e.property.1])⟩
  let ti : E.leftIndexValue (c : WithBot ℝ) b :=
    ⟨c+e.val, WithBot.coe_lt_coe.mpr (by linarith [e.property.1]), e.property.2.2⟩
  have h1 := hs si (by dsimp [si]; linarith [lt_of_lt_of_le he (min_le_left _ _)])
  have h2 := ht ti (by dsimp [ti]; linarith [lt_of_lt_of_le he (min_le_right _ _)])
  exact (dist_add_add_le _ _ _ _).trans_lt (by linarith)

theorem controlled_interior_unique : controlledInteriorUnique := by
  intro k f a b u v c L M hL hM
  rcases hL with ⟨l, m, r, hl, hm, hr, rfl⟩
  rcases hM with ⟨l', m', r', hl', hm', hr', rfl⟩
  rw [Improper.left_unique k f a u l l' hl hl', interior_unique k f u v c m m' hm hm',
    Improper.right_unique k f v b r r' hr hr']

theorem controlled_interior_integral_hasValue : controlledInteriorIntegralHasValue := by
  intro k f a b u v c h
  exact Classical.choose_spec h

theorem controlled_interior_integral_eq : controlledInteriorIntegralEq := by
  intro k f a b u v c h L hL
  exact controlled_interior_unique k f a b u v c _ L
    (controlled_interior_integral_hasValue k f a b u v c h) hL

theorem controlled_interior_of_independent : controlledInteriorOfIndependent := by
  intro k f a b c u v L M hL hM
  obtain ⟨hlocalL, l, x, hl, hx, rfl⟩ :=
    (Improper.hasIntegral_at_every_split k f a (c : WithTop ℝ) u L).mp hL
  obtain ⟨hlocalR, y, r, hy, hr, rfl⟩ :=
    (Improper.hasIntegral_at_every_split k f (c : WithBot ℝ) b v M).mp hM
  refine ⟨l, x+y, r, hl, interior_of_independent k f u.val v.val c x y hx hy, hr, ?_⟩
  abel

theorem controlled_interior_formula : controlledInteriorFormula := by
  intro k f a b c u v hlocalL hlocalR l r hl hr h t
  let d : V.regularPointValue a (c : WithTop ℝ) :=
    ⟨c-t.val, u.property.1.trans (WithBot.coe_lt_coe.mpr t.property.2.1),
      WithTop.coe_lt_coe.mpr (by linarith [t.property.1])⟩
  let e : V.regularPointValue (c : WithBot ℝ) b :=
    ⟨c+t.val, WithBot.coe_lt_coe.mpr (by linarith [t.property.1]),
      (WithTop.coe_lt_coe.mpr t.property.2.2).trans v.property.2⟩
  let si : E.rightIndexValue u.val (c : WithTop ℝ) :=
    ⟨c-t.val, t.property.2.1, d.property.2⟩
  let ti : E.leftIndexValue (c : WithBot ℝ) v.val :=
    ⟨c+t.val, e.property.1, t.property.2.2⟩
  have hd : Improper.regularIntegral k f hlocalL u d =
      E.rightTruncationValue k f u.val (c : WithTop ℝ) h.1 si := by
    simp [Improper.regularIntegral, E.rightTruncationValue, d, si,
      t.property.2.1.le]
  have he : Improper.regularIntegral k f hlocalR v e =
      -E.leftTruncationValue k f (c : WithBot ℝ) v.val h.2 ti := by
    simp [Improper.regularIntegral, E.leftTruncationValue, e, ti,
      not_le.mpr t.property.2.2, min_eq_right t.property.2.2.le, max_eq_left t.property.2.2.le]
  have hleft := Improper.left_change_split k f hlocalL u d l hl
  have hright := Improper.right_change_split k f hlocalR v e r hr
  rw [hd] at hleft
  rw [he, sub_neg_eq_add] at hright
  refine ⟨_, _, hleft, hright, ?_⟩
  change (l + E.rightTruncationValue k f u.val (c : WithTop ℝ) h.1 si) +
    (r + E.leftTruncationValue k f (c : WithBot ℝ) v.val h.2 ti) =
    l + (E.rightTruncationValue k f u.val (c : WithTop ℝ) h.1 si +
      E.leftTruncationValue k f (c : WithBot ℝ) v.val h.2 ti) + r
  abel

/-- The symmetric expanding intervals eventually contain any fixed core. -/
private theorem wholeLine_large (center u v A : ℝ) :
    ∃ t : WholeLineIndex center u v, A < t.val := by
  let R := max (max A 0) (max (center-u) (v-center)) + 1
  have hA : A < R := (le_max_left A 0).trans (le_max_left _ _) |>.trans_lt (lt_add_one _)
  have h0 : 0 < R := (le_max_right A 0).trans (le_max_left _ _) |>.trans_lt (lt_add_one _)
  have hu : center-u < R := (le_max_left (center-u) (v-center)).trans (le_max_right _ _) |>.trans_lt (lt_add_one _)
  have hv : v-center < R := (le_max_right (center-u) (v-center)).trans (le_max_right _ _) |>.trans_lt (lt_add_one _)
  exact ⟨⟨R, h0, by linarith, by linarith⟩, hA⟩

theorem whole_line_unique : wholeLineUnique := by
  intro k f center u v J L M hL hM
  rcases hL with ⟨_, h, hL⟩
  rcases hM with ⟨_, h', hM⟩
  apply eq_of_dist_eq_zero
  apply le_antisymm _ dist_nonneg
  by_contra hn
  have hd : 0 < dist L M := lt_of_not_ge hn
  obtain ⟨A, _, hA⟩ := hL (dist L M/2) (half_pos hd)
  obtain ⟨B, _, hB⟩ := hM (dist L M/2) (half_pos hd)
  obtain ⟨t, ht⟩ := wholeLine_large center u v (max A B)
  have h1 := hA t ((le_max_left _ _).trans_lt ht)
  have h2 := hB t ((le_max_right _ _).trans_lt ht)
  have htri := dist_triangle_left L M (wholeLineTruncation k f center u v J h t)
  linarith

theorem whole_line_integral_hasValue : wholeLineIntegralHasValue := by
  intro k f center u v J h
  exact Classical.choose_spec h

theorem whole_line_integral_eq : wholeLineIntegralEq := by
  intro k f center u v J h L hL
  exact whole_line_unique k f center u v J _ L
    (whole_line_integral_hasValue k f center u v J h) hL

theorem whole_line_of_independent : wholeLineOfIndependent := by
  intro k f center u v J l r huv hcore hl hr
  rcases hl with ⟨hlreg, hl⟩
  rcases hr with ⟨hrreg, hr⟩
  let h : WholeLineRegular k f u v := ⟨huv, hlreg, hrreg⟩
  refine ⟨hcore, h, fun η hη => ?_⟩
  obtain ⟨s, hs⟩ := hl (η/2) (half_pos hη)
  obtain ⟨t, ht⟩ := hr (η/2) (half_pos hη)
  let A := max 0 (max (center-s.val) (t.val-center)) + 1
  have hA : 0 < A := (le_max_left _ _).trans_lt (lt_add_one _)
  refine ⟨A, hA, fun e he => ?_⟩
  let si : E.leftIndexValue ⊥ u := ⟨center-e.val, WithBot.bot_lt_coe _, e.property.2.1⟩
  let ti : E.rightIndexValue v ⊤ := ⟨center+e.val, e.property.2.2, WithTop.coe_lt_top _⟩
  have hAs : center-s.val < A :=
    (le_max_left _ _).trans (le_max_right _ _) |>.trans_lt (lt_add_one _)
  have hAt : t.val-center < A :=
    (le_max_right _ _).trans (le_max_right _ _) |>.trans_lt (lt_add_one _)
  have h1 := hs si (by dsimp [si]; linarith)
  have h2 := ht ti (by dsimp [ti]; linarith)
  have hh := dist_add_add_le
    (E.leftTruncationValue k f ⊥ u hlreg si + J)
    (E.rightTruncationValue k f v ⊤ hrreg ti) (l+J) r
  rw [dist_add_right] at hh
  exact hh.trans_lt (by linarith)

theorem whole_line_of_ordinary : wholeLineOfOrdinary := by
  intro k f center L hL
  let c : V.regularPointValue ⊥ ⊤ :=
    ⟨center, WithBot.bot_lt_coe _, WithTop.coe_lt_top _⟩
  obtain ⟨_, l, r, hl, hr, rfl⟩ :=
    (Improper.hasIntegral_at_every_split k f ⊥ ⊤ c L).mp hL
  have hcore : CoreHasIntegral k f center center 0 := by
    refine Or.inl ⟨integrable_degenerate k f center, ?_⟩
    cases k <;> exact integral_degenerate _ f center _
  simpa only [add_zero] using
    whole_line_of_independent k f center center center 0 l r le_rfl hcore hl hr

/-- Proper interval splitting, for exactly the real/complex Darboux APIs. -/
private theorem proper_add (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : I.scalarIntegrableValue k f a b) (h2 : I.scalarIntegrableValue k f b c) :
    ∃ h : I.scalarIntegrableValue k f a c,
      I.scalarIntegralValue k f h = I.scalarIntegralValue k f h1 + I.scalarIntegralValue k f h2 := by
  cases k with
  | real =>
    obtain ⟨M, hM⟩ := BoundedOnInterval.abs_bound (RealIntegrable.bounded h1)
    obtain ⟨N, hN⟩ := BoundedOnInterval.abs_bound (RealIntegrable.bounded h2)
    have hbnd : BoundedOnInterval f a c := boundedOnInterval_of_abs (M := max M N) (by
      intro x hx
      by_cases hxb : x ≤ b
      · exact (hM x ⟨hx.1, hxb⟩).trans (le_max_left _ _)
      · exact (hN x ⟨(not_le.mp hxb).le, hx.2⟩).trans (le_max_right _ _))
    obtain ⟨hi, hv⟩ := real_split f hab hbc hbnd
    let h := hi.mpr ⟨h1, h2⟩
    exact ⟨h, hv h h1 h2⟩
  | complex =>
    obtain ⟨M, hM⟩ := ComplexIntegrable.norm_bound h1
    obtain ⟨N, hN⟩ := ComplexIntegrable.norm_bound h2
    have hbnd : ∃ B : ℝ, ∀ x ∈ Set.Icc a c, ‖f x‖ ≤ B := by
      refine ⟨max M N, fun x hx => ?_⟩
      by_cases hxb : x ≤ b
      · exact (hM x ⟨hx.1, hxb⟩).trans (le_max_left _ _)
      · exact (hN x ⟨(not_le.mp hxb).le, hx.2⟩).trans (le_max_right _ _)
    obtain ⟨hi, hv⟩ := complex_split f hab hbc hbnd
    let h := hi.mpr ⟨h1, h2⟩
    exact ⟨h, hv h h1 h2⟩

theorem whole_line_proper_formula : wholeLineProperFormula := by
  intro k f center u v J h t hc hJ
  let si : E.leftIndexValue ⊥ u := ⟨center-t.val, WithBot.bot_lt_coe _, t.property.2.1⟩
  let ti : E.rightIndexValue v ⊤ := ⟨center+t.val, t.property.2.2, WithTop.coe_lt_top _⟩
  obtain ⟨hmid, hmidEq⟩ := proper_add k f t.property.2.1.le h.1 (h.2.1.2 si) hc
  obtain ⟨hp, hpEq⟩ := proper_add k f (t.property.2.1.le.trans h.1) t.property.2.2.le
    hmid (h.2.2.2 ti)
  refine ⟨hp, ?_⟩
  rw [hpEq, hmidEq, hJ]
  rfl

end SingleVariableAnalysis.Riemann.PrincipalValue
