import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OscillatoryExample
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Dirichlet
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Necessary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option backward.isDefEq.respectTransparency false

/-!
The signed integral uses Dirichlet with primitive cos(1) - cos(t) and multiplier 1/t.
For the absolute integral, the intervals centered at π/2 + kπ with radius 1/2
lie in successive π-cells. Sine has modulus at least 1/2 there, so each proper
integral contributes at least 1/(2(k+1)π). Proper additivity and positivity sum
these contributions; harmonic divergence makes the truncations unbounded.
All values below are the shared proof-indexed Darboux integral, not a total
measure integral of the conditionally convergent function.
-/
namespace SingleVariableAnalysis.Riemann.Improper
open Set
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch10.OscillatoryExample
open scoped BigOperators

private theorem sine_integral {a b : ℝ} (hab : a ≤ b)
    (h : RealIntegrable Real.sin a b) :
    realIntegral _ h = Real.cos a - Real.cos b := by
  have he := real_ftc_second (fun x => -Real.cos x) Real.sin a b hab
    Real.continuous_cos.neg.continuousOn (fun x _ => by
      convert (Real.hasDerivAt_cos x).neg using 1; simp) h
  linarith

theorem sine_over_x_converges : sineOverXConverges := by
  have hf : RightRegular .real Real.sin 1 ⊤ :=
    ⟨WithTop.coe_lt_top _, fun t =>
      realIntegrable_of_continuousOn t.property.1.le Real.continuous_sin.continuousOn⟩
  have hd (x : ℝ) (hx : x ≠ 0) :
      HasDerivAt (fun x : ℝ => 1 / x) (-1 / x ^ 2) x := by
    simpa only [one_div, neg_div, one_mul] using hasDerivAt_inv hx
  have hc (t : RightIndex 1 ⊤) :
      ContinuousOn (fun x : ℝ => 1 / x) (Icc 1 t.val) ∧
      ContinuousOn (fun x : ℝ => -1 / x ^ 2) (Icc 1 t.val) ∧
      ∀ x ∈ Ioo 1 t.val, HasDerivAt (fun x : ℝ => 1 / x) (-1 / x ^ 2) x := by
    refine ⟨continuousOn_const.div continuousOn_id (fun x hx => by linarith [hx.1]),
      continuousOn_const.div (continuousOn_id.pow 2) (fun x hx => pow_ne_zero _ (by linarith [hx.1])),
      fun x hx => hd x (by linarith [hx.1])⟩
  have hb (t : RightIndex 1 ⊤) : ‖RightTruncation .real Real.sin 1 ⊤ hf t‖ ≤ 2 := by
    change |realIntegral Real.sin (hf.2 t)| ≤ 2
    rw [sine_integral t.property.1.le]
    exact (abs_sub _ _).trans (by linarith [Real.abs_cos_le_one (1 : ℝ), Real.abs_cos_le_one t.val])
  have hz : ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex 1 ⊤,
      ∀ t : RightIndex 1 ⊤, r.val < t.val → |1 / t.val| < ε := by
    intro ε hε
    refine ⟨⟨max 2 (1 / ε), by simp, WithTop.coe_lt_top _⟩, ?_⟩
    intro t ht
    have htp : 0 < t.val := lt_trans zero_lt_one t.property.1
    rw [abs_of_pos (one_div_pos.mpr htp)]
    exact (one_div_lt htp hε).mpr ((le_max_right _ _).trans_lt ht)
  have hm : AntitoneOn (fun x : ℝ => 1 / x)
      {x | 1 ≤ x ∧ (x : WithTop ℝ) < ⊤} := by
    intro x hx y hy hxy
    exact one_div_le_one_div_of_le (by linarith [hx.1]) hxy
  have h := right_dirichlet .real Real.sin (fun x => 1 / x)
    (fun x => -1 / x ^ 2) 1 ⊤ hf 2 hb hc (Or.inr hm) hz
  simpa only [sineOverXConverges, Specs.SingleVariableAnalysis.Ch10.Dirichlet.weighted,
    div_eq_mul_inv, one_mul] using h

private theorem absolute_continuous {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x => |Real.sin x| / x) (Icc a b) :=
  Real.continuous_sin.abs.continuousOn.div continuousOn_id (fun _ hx => ne_of_gt (ha.trans_le hx.1))

private theorem absolute_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    RealIntegrable (fun x => |Real.sin x| / x) a b :=
  realIntegrable_of_continuousOn hab (absolute_continuous ha)

/-- The fixed radius 1/2 works by the Lipschitz estimate for sine. -/
theorem sine_recurring_bound (k : ℕ) (x : ℝ)
    (hx : x ∈ Icc (Real.pi / 2 + k * Real.pi - 1 / 2)
      (Real.pi / 2 + k * Real.pi + 1 / 2)) :
    (1 : ℝ) / 2 ≤ |Real.sin x| := by
  have hc : |Real.sin (Real.pi / 2 + k * Real.pi)| = 1 := by
    rw [Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one, abs_pow]
    norm_num
  have hd := Real.abs_sin_sub_sin_le x (Real.pi / 2 + k * Real.pi)
  have he : |x - (Real.pi / 2 + k * Real.pi)| ≤ (1 : ℝ) / 2 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have ht := abs_sub_abs_le_abs_sub (Real.sin (Real.pi / 2 + k * Real.pi)) (Real.sin x)
  rw [abs_sub_comm] at ht
  linarith

private theorem interval_geometry (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ Real.pi / 2 + k * Real.pi - 1 / 2 ∧
    (k : ℝ) * Real.pi ≤ Real.pi / 2 + k * Real.pi - 1 / 2 ∧
    Real.pi / 2 + k * Real.pi + 1 / 2 ≤ (k + 1 : ℝ) * Real.pi := by
  have hp := Real.pi_gt_three
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : Real.pi ≤ (k : ℝ) * Real.pi := by nlinarith
  constructor
  · linarith
  constructor <;> nlinarith

private theorem constant_integral {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    ∃ h : RealIntegrable (fun _ => c) a b, realIntegral _ h = (b - a) * c := by
  let h : RealIntegrable (fun _ => c) a b := realIntegrable_of_continuousOn hab continuousOn_const
  refine ⟨h, ?_⟩
  have he := real_ftc_second (fun x => c * x) (fun _ => c) a b hab
    (continuous_const.mul continuous_id).continuousOn
    (fun x _ => by simpa using (hasDerivAt_id x).const_mul c) h
  change realIntegral _ h = c * b - c * a at he
  exact he.trans (by ring)

/-- Each translated interval contributes a fixed multiple of a harmonic term. -/
theorem sine_recurring_integral (k : ℕ) (hk : 1 ≤ k) :
    ∃ h : RealIntegrable (fun x => |Real.sin x| / x)
      (Real.pi / 2 + k * Real.pi - 1 / 2) (Real.pi / 2 + k * Real.pi + 1 / 2),
      (1 / 2 : ℝ) / ((k + 1 : ℝ) * Real.pi) ≤ realIntegral _ h := by
  let l := Real.pi / 2 + k * Real.pi - 1 / 2
  let u := Real.pi / 2 + k * Real.pi + 1 / 2
  have hg := interval_geometry k hk
  have hlu : l ≤ u := by dsimp [l, u]; linarith
  have hl : 0 < l := lt_of_lt_of_le zero_lt_one hg.1
  let h := absolute_integrable hl hlu
  obtain ⟨hc, hcv⟩ := constant_integral hlu ((1 / 2 : ℝ) / ((k + 1 : ℝ) * Real.pi))
  refine ⟨h, ?_⟩
  have hm := realIntegral_mono _ _ hc h (fun x hx => by
    have hxpos : 0 < x := hl.trans_le hx.1
    have hxupper : x ≤ (k + 1 : ℝ) * Real.pi := hx.2.trans hg.2.2
    exact (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 2) hxpos hxupper).trans
      (div_le_div_of_nonneg_right (sine_recurring_bound k x hx) hxpos.le))
  change realIntegral _ hc ≤ realIntegral _ h at hm
  rw [hcv] at hm
  have he : u - l = 1 := by dsimp [u, l]; ring
  simpa only [he, mul_one, one_mul] using hm

theorem sine_recurring_intervals : recurringIntervals := by
  refine ⟨1 / 2, by norm_num, by linarith [Real.pi_gt_three], ?_⟩
  intro k hk
  have hg := interval_geometry k hk
  exact ⟨hg.1, by linarith, hg.2.2, fun x hx => sine_recurring_bound k x hx,
    sine_recurring_integral k hk⟩

/-- Positivity and two proper splits compare a subinterval with the whole. -/
private theorem nonnegative_subinterval_le {f : ℝ → ℝ} {a l u b : ℝ}
    (hal : a ≤ l) (hlu : l ≤ u) (hub : u ≤ b)
    (hf : RealIntegrable f a b) (hi : RealIntegrable f l u)
    (hn : ∀ x ∈ Icc a b, 0 ≤ f x) : realIntegral f hi ≤ realIntegral f hf := by
  have hau := hal.trans hlu
  have hleft := hf.subinterval le_rfl hal (hlu.trans hub)
  have hmid := hf.subinterval le_rfl hau hub
  have hright := hf.subinterval hau hub le_rfl
  have he := (real_split f hau hub hf.bounded).2 hf hmid hright
  have he' := (real_split f hal hlu hmid.bounded).2 hmid hleft hi
  have hp := realIntegral_nonneg hleft (fun x hx => hn x ⟨hx.1, hx.2.trans (hlu.trans hub)⟩)
  have hp' := realIntegral_nonneg hright (fun x hx => hn x ⟨hau.trans hx.1, hx.2⟩)
  linarith

private theorem sine_cell_lower_bound (k : ℕ) (hk : 1 ≤ k)
    (h : RealIntegrable (fun x => |Real.sin x| / x)
      ((k : ℝ) * Real.pi) ((k + 1 : ℝ) * Real.pi)) :
    (1 / 2 : ℝ) / ((k + 1 : ℝ) * Real.pi) ≤ realIntegral _ h := by
  obtain ⟨hi, hival⟩ := sine_recurring_integral k hk
  have hg := interval_geometry k hk
  apply hival.trans
  apply nonnegative_subinterval_le hg.2.1 (by linarith) hg.2.2 h hi
  intro x hx
  apply div_nonneg (abs_nonneg _)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp := Real.pi_pos
  nlinarith [hx.1]

/-- Summing the recurring contributions gives the manuscript's harmonic bound. -/
private theorem sine_finite_lower_bound (N : ℕ)
    (h : RealIntegrable (fun x => |Real.sin x| / x) 1 ((N + 1 : ℝ) * Real.pi)) :
    (1 / (2 * Real.pi)) * ((∑ n ∈ Finset.range (N + 2), 1 / (n : ℝ)) - 1)
      ≤ realIntegral _ h := by
  induction N with
  | zero =>
    simpa [Finset.sum_range_succ] using realIntegral_nonneg h (fun x hx => div_nonneg (abs_nonneg _) (by linarith [hx.1]))
  | succ N ih =>
    simp only [Nat.cast_add, Nat.cast_one] at h ⊢
    have hp := Real.pi_gt_three
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hcut : 1 ≤ (N + 1 : ℝ) * Real.pi := by nlinarith
    have horder : (N + 1 : ℝ) * Real.pi ≤ (N + 1 + 1 : ℝ) * Real.pi := by
      nlinarith
    have hleft := h.subinterval le_rfl hcut horder
    have hright := h.subinterval hcut horder le_rfl
    have he := (real_split _ hcut horder h.bounded).2 h hleft hright
    have hb := sine_cell_lower_bound (N + 1) (by omega) (by simpa only [Nat.cast_add, Nat.cast_one] using hright)
    have hprev := ih hleft
    rw [Finset.sum_range_succ]
    push_cast
    have hterm : (1 / (2 * Real.pi)) * (1 / (N + 2 : ℝ)) =
        (1 / 2 : ℝ) / (((N + 1 : ℕ) + 1 : ℝ) * Real.pi) := by
      push_cast
      field_simp; ring
    change realIntegral _ h = realIntegral _ hleft + realIntegral _ hright at he
    simp only [Nat.cast_add, Nat.cast_one] at hb
    push_cast at hterm
    have hb' : (1 / (2 * Real.pi)) * (1 / (N + 2 : ℝ)) ≤ realIntegral _ hright := by
      rw [hterm]
      exact hb
    nlinarith only [hprev, hb', he]

theorem sine_harmonic_lower_bound : harmonicLowerBound := by
  refine ⟨1 / (2 * Real.pi), by positivity, fun N => ?_⟩
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hab : 1 ≤ (N + 1 : ℝ) * Real.pi := by nlinarith [Real.pi_gt_three]
  let h := absolute_integrable zero_lt_one hab
  exact ⟨h, sine_finite_lower_bound N h⟩

theorem sine_absolute_diverges : absoluteDiverges := by
  have hf : RightRegular .real (fun x => |Real.sin x| / x) 1 ⊤ :=
    ⟨WithTop.coe_lt_top _, fun t => absolute_integrable zero_lt_one t.property.1.le⟩
  apply right_nonnegative_diverges_of_unbounded _ 1 ⊤ hf
    (fun x hx _ => div_nonneg (abs_nonneg _) (by linarith))
  rintro ⟨B, hB⟩
  let c := 1 / (2 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N, hN⟩ := harmonic_partialSums_unbounded (B / c + 1)
  have hmono : realPartialSum (fun n : ℕ => 1 / (n : ℝ)) N ≤
      ∑ n ∈ Finset.range (N + 2), 1 / (n : ℝ) := by
    change (∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ)) ≤ _
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro i _ _
    positivity
  have hcut : 1 < (N + 1 : ℝ) * Real.pi := by
    have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [Real.pi_gt_three]
  let t : RightIndex 1 ⊤ := ⟨(N + 1 : ℝ) * Real.pi, hcut, WithTop.coe_lt_top _⟩
  have hu := hB (Set.mem_range_self t)
  have hl := sine_finite_lower_bound N (hf.2 t)
  change realIntegral _ (hf.2 t) ≤ B at hu
  have hlarge : B < c * ((∑ n ∈ Finset.range (N + 2), 1 / (n : ℝ)) - 1) := by
    have hh : B / c < (∑ n ∈ Finset.range (N + 2), 1 / (n : ℝ)) - 1 := by linarith
    exact (div_lt_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  exact (not_lt_of_ge (hl.trans hu)) hlarge

theorem sine_conditional_convergence : conditionalConvergence := by
  refine ⟨sine_over_x_converges, ?_⟩
  have he (x : ℝ) (hx : 1 ≤ x) : |Real.sin x| / x = |Real.sin x / x| := by
    rw [abs_div, abs_of_pos (by linarith : 0 < x)]
  obtain ⟨hf, hdiv⟩ := sine_absolute_diverges
  have hreg : RightRegular .real (fun x : ℝ => (|Real.sin x / x| : ℝ)) 1 ⊤ := by
    refine ⟨hf.1, fun t => ?_⟩
    exact (realIntegral_congr_on (hf.2 t) (fun x hx => he x hx.1)).choose
  have hsame (t : RightIndex 1 ⊤) :
      RightTruncation .real (fun x => |Real.sin x| / x) 1 ⊤ hf t =
      RightTruncation .real (fun x : ℝ => (|Real.sin x / x| : ℝ)) 1 ⊤ hreg t := by
    exact (realIntegral_congr_on (hf.2 t) (fun x hx => he x hx.1)).choose_spec.symm
  apply right_infinite_not_converges _ 1 ⊤ (Or.inl ?_)
  refine ⟨hreg, fun B => ?_⟩
  obtain ⟨r, hr⟩ := hdiv B
  refine ⟨r, fun t ht => ?_⟩
  change B < RightTruncation .real (fun x : ℝ => (|Real.sin x / x| : ℝ)) 1 ⊤ hreg t
  exact (hr t ht).trans_eq (hsame t)

end SingleVariableAnalysis.Riemann.Improper

