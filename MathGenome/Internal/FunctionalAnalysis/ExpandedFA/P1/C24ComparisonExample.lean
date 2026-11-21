import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24ComparisonExample
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Three interval maps separate existence, uniqueness, and attraction.
All functions and all iterates below are on the actual closed-interval subtype. -/

noncomputable section
open Filter
open scoped Topology
open ExpandedFA.P1.C24ComparisonExample.Spec

namespace ExpandedFA.P1.C24ComparisonExample

/-- The common nonempty compact convex domain of all three examples. -/
theorem interval_geometry : IntervalGeometry := by
  exact ⟨⟨0, by constructor <;> norm_num⟩, isCompact_Icc, convex_Icc 0 1⟩

/-- Every point is fixed by the continuous identity, and the endpoints differ. -/
theorem identity_example : IdentityExample := by
  refine ⟨continuous_id, fun _ => rfl, ?_⟩
  intro h
  have := congrArg Subtype.val h
  norm_num [zeroPoint, onePoint] at this

/-- Reflection preserves every distance, so its Lipschitz bound is exactly one. -/
theorem interval_reflection_isometry : Isometry reflection := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [Subtype.dist_eq, dist_eq_norm, reflection]
  have h : (1 - (x : ℝ)) - (1 - (y : ℝ)) = -((x : ℝ) - (y : ℝ)) := by ring
  rw [h, norm_neg]

/-- Applying reflection twice is the identity. -/
theorem interval_reflection_involutive : Function.Involutive reflection := by
  intro x
  apply Subtype.ext
  change 1 - (1 - (x : ℝ)) = (x : ℝ)
  ring

/-- The even and odd iterates are the two points of the orbit, also at n = 0. -/
theorem interval_reflection_iterates (x : UnitInterval) (n : ℕ) :
    (reflection^[2 * n]) x = x ∧ (reflection^[2 * n + 1]) x = reflection x := by
  have heven : ∀ n : ℕ, (reflection^[2 * n]) x = x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply]
      change (reflection^[2 * n]) (reflection (reflection x)) = x
      rw [interval_reflection_involutive, ih]
  refine ⟨heven n, ?_⟩
  rw [Function.iterate_succ_apply', heven n]

/-- The two constant subsequences have different limits off the midpoint. -/
theorem interval_reflection_not_convergent (x : UnitInterval)
    (hx : (x : ℝ) ≠ 1 / 2) :
    ¬ ∃ l : ℝ, Tendsto (fun n : ℕ => ((reflection^[n]) x : ℝ)) atTop (𝓝 l) := by
  rintro ⟨l, hl⟩
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hodd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hxlim : Tendsto (fun _ : ℕ => (x : ℝ)) atTop (𝓝 l) := by
    simpa only [Function.comp_def, (interval_reflection_iterates x _).1] using hl.comp heven
  have hrlim : Tendsto (fun _ : ℕ => (reflection x : ℝ)) atTop (𝓝 l) := by
    simpa only [Function.comp_def, (interval_reflection_iterates x _).2] using hl.comp hodd
  have hxl : (x : ℝ) = l := tendsto_nhds_unique tendsto_const_nhds hxlim
  have hrl : (reflection x : ℝ) = l := tendsto_nhds_unique tendsto_const_nhds hrlim
  change 1 - (x : ℝ) = l at hrl
  apply hx
  linarith

/-- Unique fixed point does not imply attraction: reflection is the explicit
continuous, distance-preserving counterexample on a Schauder domain. -/
theorem reflection_example : ReflectionExample := by
  refine ⟨interval_reflection_isometry.continuous, interval_reflection_isometry,
    interval_reflection_isometry.lipschitzWith, ?_, ?_, ?_,
    interval_reflection_iterates, interval_reflection_not_convergent⟩
  · intro q hq
    have h := hq zeroPoint onePoint
    norm_num [reflection, zeroPoint, onePoint] at h
    exact h
  · apply Subtype.ext
    norm_num [reflection, ExpandedFA.P1.C24ComparisonExample.Spec.midpoint]
  · intro x hx
    have h := congrArg Subtype.val hx
    change 1 - (x : ℝ) = (x : ℝ) at h
    apply Subtype.ext
    change (x : ℝ) = 1 / 2
    linarith

/-- Halving has contraction factor one half in the induced interval metric. -/
theorem interval_halving_contracting : ContractingWith (1 / 2) halving := by
  constructor
  · norm_num
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Subtype.dist_eq, dist_eq_norm, halving]
    have h : (x : ℝ) / 2 - (y : ℝ) / 2 = ((x : ℝ) - (y : ℝ)) / 2 := by ring
    rw [h, norm_div]
    norm_num
    exact le_of_eq (by ring)

/-- The exact geometric orbit formula includes the initial term. -/
theorem interval_halving_iterates (x : UnitInterval) (n : ℕ) :
    ((halving^[n]) x : ℝ) = (x : ℝ) / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((halving^[n]) x : ℝ) / 2 = (x : ℝ) / 2 ^ (n + 1)
    rw [ih, pow_succ, div_div]

/-- Strict contraction supplies attraction, and here the error is exactly geometric. -/
theorem halving_example : HalvingExample := by
  refine ⟨interval_halving_contracting.2.continuous,
    interval_halving_contracting, ?_, ?_, interval_halving_iterates, ?_, ?_⟩
  · apply Subtype.ext
    norm_num [halving, zeroPoint]
  · intro x hx
    have h := congrArg Subtype.val hx
    change (x : ℝ) / 2 = (x : ℝ) at h
    apply Subtype.ext
    change (x : ℝ) = 0
    linarith
  · intro x n
    rw [interval_halving_iterates]
    simp only [zeroPoint, sub_zero, norm_div, norm_pow, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      div_pow, one_pow]
    ring
  · intro x
    have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h := hpow.const_mul (x : ℝ)
    simpa only [interval_halving_iterates, div_pow, one_pow, mul_zero, mul_one_div] using h

end ExpandedFA.P1.C24ComparisonExample
