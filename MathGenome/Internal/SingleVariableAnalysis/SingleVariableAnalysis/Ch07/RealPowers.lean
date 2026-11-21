import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogConstruction
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpAddition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.PositiveRoots
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Real powers with explicit domains

The source construction uses the previously constructed factorial-series
exponential and its inverse. The canonical bridge is proved only at positive
bases; Mathlib's power laws, continuity and limits can then be transported.
The partial interface extends to zero exactly for positive exponents.
At negative bases the separate rational operation uses odd algebraic roots,
not Mathlib's nonintegral negative-base `rpow`. Squaring at exponent 1/2
proves the obstruction to an all-real exponent law at a negative base.

Library proof provenance: `Pow/Real.lean` derives positive-base laws from
exp/log; `Pow/Continuity.lean` supplies continuity. `Pow/Asymptotics.lean`
proves positive-exponent growth by comparison with inverse powers, and
negative-exponent limits by reciprocation. Root agreement reuses the shared
supremum-root construction from Chapter 1.
-/

noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology

def realPower : ℝ → ℝ → ℝ := fun x α => realSeriesExp (α * seriesLog x)

def partialRealPower : ℝ → ℝ → Option ℝ := fun x α => if 0 < x then some (realPower x α)
  else if x = 0 ∧ 0 < α then some 0 else none

def negativeRationalPower : ℝ → ℚ → ℝ := fun x q => (-nonnegativeRoot q.den (-x)) ^ q.num

theorem realPower_eq_rpow :
    ∀ x : ℝ, 0 < x → ∀ α : ℝ, realPower x α = x ^ α := by
  intro x hx α
  unfold realPower
  rw [seriesLog_eq_realLog x hx]
  have he : realSeriesExp (α * Real.log x) = Real.exp (α * Real.log x) :=
    expSeries_eq_realExp (α * Real.log x)
  rw [he, Real.rpow_def_of_pos hx, mul_comm]

theorem realPower_pos :
    ∀ x : ℝ, 0 < x → ∀ α : ℝ, 0 < realPower x α := by
  intro x hx α
  rw [realPower_eq_rpow x hx]
  exact Real.rpow_pos_of_pos hx α

theorem realPower_add :
    ∀ x : ℝ, 0 < x → ∀ α β : ℝ,
  realPower x (α + β) = realPower x α * realPower x β := by
  intro x hx α β
  simp only [realPower_eq_rpow x hx]
  exact Real.rpow_add hx α β

theorem realPower_mul_base :
    ∀ x y : ℝ, 0 < x → 0 < y → ∀ α : ℝ,
  realPower (x * y) α = realPower x α * realPower y α := by
  intro x y hx hy α
  rw [realPower_eq_rpow _ (mul_pos hx hy), realPower_eq_rpow x hx,
    realPower_eq_rpow y hy]
  exact Real.mul_rpow hx.le hy.le

theorem realPower_mul_exponent :
    ∀ x : ℝ, 0 < x → ∀ α β : ℝ,
  realPower (realPower x α) β = realPower x (α * β) := by
  intro x hx α β
  rw [realPower_eq_rpow _ (realPower_pos x hx α), realPower_eq_rpow x hx,
    realPower_eq_rpow x hx]
  exact (Real.rpow_mul hx.le α β).symm

theorem realPower_zero_exponent :
    ∀ x : ℝ, 0 < x → realPower x 0 = 1 := by
  intro x hx
  rw [realPower_eq_rpow x hx, Real.rpow_zero]

theorem realPower_one_exponent :
    ∀ x : ℝ, 0 < x → realPower x 1 = x := by
  intro x hx
  rw [realPower_eq_rpow x hx, Real.rpow_one]

theorem realPower_int :
    ∀ x : ℝ, 0 < x → ∀ p : ℤ, realPower x (p : ℝ) = x ^ p := by
  intro x hx p
  rw [realPower_eq_rpow x hx, Real.rpow_intCast]

theorem realPower_rat :
    ∀ x : ℝ, 0 < x → ∀ q : ℚ, realPower x (q : ℝ) = rationalPower x q := by
  intro x hx q
  rw [realPower_eq_rpow x hx, rationalPower_eq_rpow x hx]

theorem realPower_fraction :
    ∀ x : ℝ, 0 < x → ∀ (p : ℤ) (d : ℕ), 0 < d →
  realPower x ((p : ℝ) / d) = nonnegativeRoot d x ^ p := by
  intro x hx p d hd
  have h := (realPower_rat x hx ((p : ℚ) / d)).trans
    (rationalPower_fraction x hx p d hd)
  simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using h

theorem realPower_fraction_pow :
    ∀ x : ℝ, 0 < x → ∀ (p : ℤ) (d : ℕ), 0 < d →
  realPower x ((p : ℝ) / d) ^ d = x ^ p := by
  intro x hx p d hd
  rw [realPower_eq_rpow x hx, ← Real.rpow_mul_natCast hx.le,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hd.ne'), Real.rpow_intCast]

theorem realPower_root :
    ∀ x : ℝ, 0 < x → ∀ d : ℕ, 0 < d →
  realPower x (1 / (d : ℝ)) = nonnegativeRoot d x := by
  intro x hx d hd
  simpa using realPower_fraction x hx (1 : ℤ) d hd

theorem realPower_joint_continuous :
    ContinuousOn (fun p : ℝ × ℝ => realPower p.1 p.2)
  {p | 0 < p.1} := by
  apply ContinuousOn.congr (f := fun p : ℝ × ℝ => p.1 ^ p.2)
  · intro p hp
    exact (Real.continuousAt_rpow p (Or.inl hp.ne')).continuousWithinAt
  · intro p hp
    exact realPower_eq_rpow p.1 hp p.2

theorem realPower_continuous_base :
    ∀ α : ℝ, ContinuousOn (fun x => realPower x α) (Ioi 0) := by
  intro α
  apply ContinuousOn.congr (f := fun x : ℝ => x ^ α)
  · intro x hx
    exact (Real.continuousAt_rpow_const x α (Or.inl hx.ne')).continuousWithinAt
  · intro x hx
    exact realPower_eq_rpow x hx α

theorem realPower_continuous_exponent :
    ∀ x : ℝ, 0 < x → Continuous (realPower x) := by
  intro x hx
  exact (Real.continuous_const_rpow hx.ne').congr (fun α => (realPower_eq_rpow x hx α).symm)

theorem realPower_strictMono_base :
    ∀ α : ℝ, 0 < α → StrictMonoOn (fun x => realPower x α) (Ioi 0) := by
  intro α hα x hx y hy hxy
  change realPower x α < realPower y α
  rw [realPower_eq_rpow x hx, realPower_eq_rpow y hy]
  exact Real.rpow_lt_rpow hx.le hxy hα

theorem realPower_strictAnti_base :
    ∀ α : ℝ, α < 0 → StrictAntiOn (fun x => realPower x α) (Ioi 0) := by
  intro α hα x hx y hy hxy
  change realPower y α < realPower x α
  rw [realPower_eq_rpow x hx, realPower_eq_rpow y hy]
  exact Real.rpow_lt_rpow_of_neg hx hxy hα

theorem realPower_strictMono_exponent :
    ∀ x : ℝ, 1 < x → StrictMono (realPower x) := by
  intro x hx α β hαβ
  rw [realPower_eq_rpow x (zero_lt_one.trans hx), realPower_eq_rpow x (zero_lt_one.trans hx)]
  exact Real.rpow_lt_rpow_of_exponent_lt hx hαβ

theorem realPower_strictAnti_exponent :
    ∀ x : ℝ, 0 < x → x < 1 → StrictAnti (realPower x) := by
  intro x hx hx1 α β hαβ
  rw [realPower_eq_rpow x hx, realPower_eq_rpow x hx]
  exact Real.rpow_lt_rpow_of_exponent_gt hx hx1 hαβ

theorem realPower_pos_tendsto_zero_right :
    ∀ α : ℝ, 0 < α → Tendsto (fun x => realPower x α) (𝓝[>] 0) (𝓝 0) := by
  intro α hα
  have h : Tendsto (fun x : ℝ => x ^ α) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ α) 0 :=
      (Real.continuous_rpow_const hα.le).continuousAt
    simpa only [Real.zero_rpow hα.ne'] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (realPower_eq_rpow x hx α).symm

theorem realPower_pos_tendsto_atTop :
    ∀ α : ℝ, 0 < α → Tendsto (fun x => realPower x α) atTop atTop := by
  intro α hα
  apply (tendsto_rpow_atTop hα).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (realPower_eq_rpow x hx α).symm

theorem realPower_neg_tendsto_zero_right :
    ∀ α : ℝ, α < 0 → Tendsto (fun x => realPower x α) (𝓝[>] 0) atTop := by
  intro α hα
  apply (tendsto_rpow_neg_nhdsGT_zero hα).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (realPower_eq_rpow x hx α).symm

theorem realPower_neg_tendsto_atTop :
    ∀ α : ℝ, α < 0 → Tendsto (fun x => realPower x α) atTop (𝓝 0) := by
  intro α hα
  have h : Tendsto (fun x : ℝ => x ^ α) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hα)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (realPower_eq_rpow x hx α).symm

theorem realPower_zero_continuous_extension :
    ∀ α : ℝ, 0 < α → ∃ f : ℝ → ℝ,
  f 0 = 0 ∧ (∀ x : ℝ, 0 < x → f x = realPower x α) ∧ ContinuousOn f (Ici 0) := by
  intro α hα
  refine ⟨fun x => x ^ α, Real.zero_rpow hα.ne', ?_,
    (Real.continuous_rpow_const hα.le).continuousOn⟩
  intro x hx
  exact (realPower_eq_rpow x hx α).symm

theorem partialRealPower_positive :
    ∀ x : ℝ, 0 < x → ∀ α : ℝ,
  partialRealPower x α = some (realPower x α) := by
  intro x hx α
  simp [partialRealPower, hx]

theorem partialRealPower_zero :
    ∀ α : ℝ, 0 < α → partialRealPower 0 α = some 0 := by
  intro α hα
  simp [partialRealPower, hα]

theorem partialRealPower_domain :
    ∀ x α : ℝ, (partialRealPower x α).isSome = true ↔
  0 < x ∨ (x = 0 ∧ 0 < α) := by
  intro x α
  unfold partialRealPower
  split_ifs <;> simp_all

theorem partialRealPower_zero_undefined :
    ∀ α : ℝ, α ≤ 0 → partialRealPower 0 α = none := by
  intro α hα
  simp [partialRealPower, not_lt.mpr hα]

theorem partialRealPower_negative_undefined :
    ∀ x : ℝ, x < 0 → ∀ α : ℝ, partialRealPower x α = none := by
  intro x hx α
  simp [partialRealPower, not_lt.mpr hx.le, hx.ne]

theorem negativeRationalPower_root :
    ∀ x : ℝ, x < 0 → ∀ q : ℚ, Odd q.den →
  negativeRationalPower x q ^ q.den = x ^ q.num := by
  intro x hx q hq
  have hr : (-nonnegativeRoot q.den (-x)) ^ q.den = x := by
    rw [hq.neg_pow, nonnegativeRoot_pow q.den q.den_pos (-x) (neg_nonneg.mpr hx.le), neg_neg]
  unfold negativeRationalPower
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hr]

theorem negativeRationalPower_unique :
    ∀ x : ℝ, x < 0 → ∀ q : ℚ, Odd q.den →
  ∀ y : ℝ, y ^ q.den = x ^ q.num → y = negativeRationalPower x q := by
  intro x hx q hq y hy
  exact hq.pow_injective (hy.trans (negativeRationalPower_root x hx q hq).symm)

theorem negativeRationalPower_int :
    ∀ x : ℝ, x < 0 → ∀ p : ℤ,
  negativeRationalPower x (p : ℚ) = x ^ p := by
  intro x hx p
  have h : nonnegativeRoot 1 (-x) = -x := by
    simpa only [pow_one] using nonnegativeRoot_pow 1 (by decide) (-x) (neg_nonneg.mpr hx.le)
  simp [negativeRationalPower, h]

theorem negative_base_no_all_real_power_laws :
    ∀ x : ℝ, x < 0 →
  ¬ ∃ P : ℝ → ℝ, P 1 = x ∧ ∀ α β : ℝ, P (α + β) = P α * P β := by
  intro x hx ⟨P, h1, hadd⟩
  have h := hadd (1/2) (1/2)
  norm_num at h
  rw [h1] at h
  have hn := mul_self_nonneg (P (1/2))
  linarith

end SingleVariableAnalysis
