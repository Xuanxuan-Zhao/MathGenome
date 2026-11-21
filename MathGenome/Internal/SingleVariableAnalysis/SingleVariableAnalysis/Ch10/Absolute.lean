import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.SeveralEndpoints
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Absolute

/-! Absolute convergence of improper Darboux integrals. Proper norm inequalities
transfer Cauchy tails to f. The same inequalities pass to the endpoint limits;
finite totals use the triangle inequality only after all endpoint limits exist. -/
namespace SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch10.Absolute
open scoped BigOperators

noncomputable abbrev RightAbsoluteConverges : rightAbsoluteType := rightAbsoluteValue
noncomputable abbrev RightConditionallyConverges : rightConditionalType := rightConditionalValue
noncomputable abbrev LeftAbsoluteConverges : leftAbsoluteType := leftAbsoluteValue
noncomputable abbrev LeftConditionallyConverges : leftConditionalType := leftConditionalValue
noncomputable abbrev AbsoluteConverges : absoluteType := absoluteValue
noncomputable abbrev ConditionallyConverges : conditionalType := conditionalValue
noncomputable abbrev FiniteAbsoluteConverges : finiteAbsoluteType := finiteAbsoluteValue
noncomputable abbrev FiniteConditionallyConverges : finiteConditionalType := finiteConditionalValue

/-- The proper scalar integral and its real norm integral, for exactly ℝ or ℂ. -/
theorem scalar_integral_norm_le (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a b : ℝ} (h : I.scalarIntegrableValue k f a b) :
    ∃ hn : I.scalarIntegrableValue .real (fun x => ‖f x‖) a b,
      ‖I.scalarIntegralValue k f h‖ ≤ I.scalarIntegralValue .real _ hn := by
  cases k with
  | real =>
    obtain ⟨hn, hb, _⟩ := real_norm_estimate f h
    exact ⟨hn, hb⟩
  | complex =>
    obtain ⟨hn, hb, _⟩ := complex_norm_estimate f h
    exact ⟨hn, hb⟩

theorem right_absolute_converges : rightAbsoluteConverges := by
  intro k f a b h habs
  rcases habs with ⟨A, hn, hA⟩
  apply (right_cauchy_criterion k f a b h).mpr
  intro ε hε
  obtain ⟨r, hr⟩ := (right_cauchy_criterion .real (fun x => ‖f x‖) a b hn).mp
    ⟨A, hn, hA⟩ ε hε
  refine ⟨r, fun u v hru huv => ?_⟩
  obtain ⟨hf, _⟩ := right_tail_difference k f a b h u v huv
  obtain ⟨hn', hlt⟩ := hr u v hru huv
  obtain ⟨hn'', hle⟩ := scalar_integral_norm_le k f hf
  refine ⟨hf, lt_of_le_of_lt hle ?_⟩
  exact lt_of_le_of_lt (le_abs_self _) hlt

theorem left_absolute_converges : leftAbsoluteConverges := by
  intro k f a b h habs
  rcases habs with ⟨A, hn, hA⟩
  apply (left_cauchy_criterion k f a b h).mpr
  intro ε hε
  obtain ⟨r, hr⟩ := (left_cauchy_criterion .real (fun x => ‖f x‖) a b hn).mp
    ⟨A, hn, hA⟩ ε hε
  refine ⟨r, fun u v huv hvr => ?_⟩
  obtain ⟨hf, _⟩ := left_tail_difference k f a b h u v huv
  obtain ⟨hn', hlt⟩ := hr u v huv hvr
  obtain ⟨hn'', hle⟩ := scalar_integral_norm_le k f hf
  refine ⟨hf, lt_of_le_of_lt hle ?_⟩
  exact lt_of_le_of_lt (le_abs_self _) hlt

/-- A quantitative form of passing a finite norm bound to a limit. -/
private theorem norm_bound_from_approximations {Y : Type*} [NormedAddCommGroup Y]
    (x L : Y) (y A ε : ℝ) (hxy : ‖x‖ ≤ y)
    (hx : dist x L < ε) (hy : |y - A| < ε) : ‖L‖ < A + 2 * ε := by
  have hx' : ‖x - L‖ < ε := by simpa only [dist_eq_norm] using hx
  have htri := norm_sub_norm_le L x
  rw [norm_sub_rev] at htri
  linarith only [hx', htri, hxy, (abs_lt.mp hy).2]

theorem right_norm_bound : rightNormBound := by
  intro k f a b L A hL hA
  rcases hL with ⟨hf, hL⟩
  rcases hA with ⟨hn, hA⟩
  by_contra hnot
  have hp : 0 < ‖L‖ - A := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨r, hr⟩ := hL ((‖L‖ - A) / 3) (by positivity)
  obtain ⟨s, hs⟩ := hA ((‖L‖ - A) / 3) (by positivity)
  obtain ⟨t, hrt, hst⟩ := right_later r s
  have h1 := hr t hrt
  have h2 := hs t hst
  obtain ⟨hn', hle⟩ := scalar_integral_norm_le k f (hf.2 t)
  change ‖RightTruncation k f a b hf t‖ ≤
    RightTruncation .real (fun x => ‖f x‖) a b hn t at hle
  change |(show ℝ from RightTruncation .real (fun x => ‖f x‖) a b hn t) - A| < _ at h2
  have hh := norm_bound_from_approximations (RightTruncation k f a b hf t) L
    (show ℝ from RightTruncation .real (fun x => ‖f x‖) a b hn t) A
    ((‖L‖ - A) / 3) hle h1 h2
  change ‖L‖ < A + 2 * ((‖L‖ - A) / 3) at hh
  linarith only [hh, hp]

theorem left_norm_bound : leftNormBound := by
  intro k f a b L A hL hA
  rcases hL with ⟨hf, hL⟩
  rcases hA with ⟨hn, hA⟩
  by_contra hnot
  have hp : 0 < ‖L‖ - A := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨r, hr⟩ := hL ((‖L‖ - A) / 3) (by positivity)
  obtain ⟨s, hs⟩ := hA ((‖L‖ - A) / 3) (by positivity)
  obtain ⟨t, hrt, hst⟩ := left_earlier r s
  have h1 := hr t hrt
  have h2 := hs t hst
  obtain ⟨hn', hle⟩ := scalar_integral_norm_le k f (hf.2 t)
  change ‖LeftTruncation k f a b hf t‖ ≤
    LeftTruncation .real (fun x => ‖f x‖) a b hn t at hle
  change |(show ℝ from LeftTruncation .real (fun x => ‖f x‖) a b hn t) - A| < _ at h2
  have hh := norm_bound_from_approximations (LeftTruncation k f a b hf t) L
    (show ℝ from LeftTruncation .real (fun x => ‖f x‖) a b hn t) A
    ((‖L‖ - A) / 3) hle h1 h2
  change ‖L‖ < A + 2 * ((‖L‖ - A) / 3) at hh
  linarith only [hh, hp]

/-- Local proper integrability restricts to each independently chosen side. -/
theorem local_left_regular (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c : RegularPoint a b) : LeftRegular k f a c.val :=
  ⟨c.property.1, fun t => h _ _ t.property.1 t.property.2.le c.property.2⟩

theorem local_right_regular (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c : RegularPoint a b) : RightRegular k f c.val b :=
  ⟨c.property.2, fun t => h _ _ c.property.1 t.property.1.le t.property.2⟩

theorem absolute_converges : absoluteConverges := by
  intro k f a b h habs
  rcases habs with ⟨A, _, c, l, r, hl, hr, _⟩
  have hleft := left_absolute_converges k f a c.val
    (local_left_regular k f h c) ⟨l, hl⟩
  have hright := right_absolute_converges k f c.val b
    (local_right_regular k f h c) ⟨r, hr⟩
  obtain ⟨L, hL⟩ := (split_existence k f a b c).mp ⟨hleft, hright⟩
  exact ⟨L, h, c, hL⟩

/-- The triangle inequality combines two finite endpoint values. -/
theorem split_norm_bound (k : ScalarKind) (f : ℝ → S.scalarValue k)
    (a : WithBot ℝ) (b : WithTop ℝ) (c : RegularPoint a b)
    (L : S.scalarValue k) (A : ℝ)
    (hf : HasIntegralAtSplit k f a b c L)
    (hn : HasIntegralAtSplit .real (fun x => ‖f x‖) a b c A) : ‖L‖ ≤ A := by
  rcases hf with ⟨l, r, hl, hr, rfl⟩
  rcases hn with ⟨l', r', hl', hr', rfl⟩
  exact (norm_add_le l r).trans
    (add_le_add (left_norm_bound k f a c.val l l' hl hl')
      (right_norm_bound k f c.val b r r' hr hr'))

theorem norm_bound : normBound := by
  intro k f a b L A hf hn
  obtain ⟨_, c, hc⟩ := hf
  have hn' := ((hasIntegral_at_every_split .real (fun x => ‖f x‖) a b c A).mp hn).2
  exact split_norm_bound k f a b c L A hc hn'

theorem absolute_at_every_split : absoluteAtEverySplit := by
  intro k f a b c
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨h, l, r, hl, hr, _⟩ :=
      (hasIntegral_at_every_split .real (fun x => ‖f x‖) a b c A).mp hA
    exact ⟨h, ⟨l, hl⟩, ⟨r, hr⟩⟩
  · rintro ⟨h, ⟨l, hl⟩, ⟨r, hr⟩⟩
    exact ⟨l + r, h, c, l, r, hl, hr, rfl⟩

theorem finite_absolute_converges : finiteAbsoluteConverges := by
  intro k f n a b s c h habs
  have hn := (finite_existence .real (fun x => ‖f x‖) n a b s c).mp habs
  apply (finite_existence k f n a b s c).mpr
  intro i
  exact ⟨h i,
    left_absolute_converges k f _ _ (local_left_regular k f (h i) (c i)) (hn i).2.1,
    right_absolute_converges k f _ _ (local_right_regular k f (h i) (c i)) (hn i).2.2⟩

theorem finite_norm_bound : finiteNormBound := by
  intro k f n a b s c L A hf hn
  rcases hf with ⟨v, hv, rfl⟩
  rcases hn with ⟨w, hw, rfl⟩
  change ‖∑ i, v i‖ ≤ ∑ i, (show ℝ from w i)
  calc
    ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (show ℝ from w i) := Finset.sum_le_sum fun i _ =>
      split_norm_bound k f _ _ (c i) (v i) (w i) (hv i).2 (hw i).2

theorem finite_absolute_endpoints : finiteAbsoluteEndpoints := by
  intro k f n a b s c
  exact finite_existence .real (fun x => ‖f x‖) n a b s c

end SingleVariableAnalysis.Riemann.Improper
