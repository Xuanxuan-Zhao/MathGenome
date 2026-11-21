import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpProperties
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.FlatDecay
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
namespace SingleVariableAnalysis

open Filter
open scoped Topology BigOperators

/-- The zero extension of the exponential in the manuscript's flat example. -/
def flatExponential (x : ℝ) : ℝ :=
  if x = 0 then 0 else realSeriesExp (-1 / x ^ 2)

@[simp] theorem flatExponential_zero : flatExponential 0 = 0 := by
  simp [flatExponential]

theorem flatExponential_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    flatExponential x = realSeriesExp (-1 / x ^ 2) := by
  simp [flatExponential, hx]

private theorem inverse_square_tendsto :
    Tendsto (fun x : ℝ => (x ^ 2)⁻¹) (𝓝[≠] 0) atTop := by
  have h := (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
    (tendsto_norm_inv_nhdsNE_zero_atTop (α := ℝ))
  simpa only [Function.comp_def, Real.norm_eq_abs, sq_abs, inv_pow] using h

/-- The source estimate for every nonnegative integer order. -/
theorem flatExponential_inversePower_decay :
    Specs.SingleVariableAnalysis.Ch06.FlatDecay.inversePowerDecay := by
  intro N
  change Tendsto (fun x : ℝ => |x| ^ (-(N : ℤ)) * realSeriesExp (-1 / x ^ 2))
    (𝓝[≠] 0) (𝓝 0)
  have hExp : realSeriesExp = Real.exp := funext expSeries_eq_realExp
  have hu := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp
    inverse_square_tendsto
  have hb : ∀ᶠ x : ℝ in 𝓝[≠] 0, |x| ≤ 1 := by
    filter_upwards [((continuous_abs.tendsto 0).eventually
      (gt_mem_nhds (show |(0 : ℝ)| < 1 by norm_num))).filter_mono nhdsWithin_le_nhds]
      with x hx using hx.le
  apply squeeze_zero' (Eventually.of_forall fun x => by
    rw [hExp]
    positivity) ?_ hu
  filter_upwards [hb, self_mem_nhdsWithin] with x hx hx0
  have hne : x ≠ 0 := hx0
  have hsq : x ^ 2 ≤ |x| := by nlinarith [sq_abs x, abs_nonneg x]
  have hi : |x|⁻¹ ≤ (x ^ 2)⁻¹ :=
    (inv_le_inv₀ (abs_pos.mpr hne) (sq_pos_of_ne_zero hne)).mpr hsq
  rw [hExp, neg_div, one_div, zpow_neg, zpow_natCast, ← inv_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hi N) (Real.exp_pos _).le

/-- The extension remains positive at every nonzero real argument. -/
theorem flatExponential_pos :
    Specs.SingleVariableAnalysis.Ch06.FlatDecay.positiveOffZero := by
  intro x hx
  change 0 < flatExponential x
  rw [flatExponential_of_ne_zero hx]
  exact real_expSeries_pos _

/-- Every finite power order has an arbitrarily small relative error,
including at the extension point itself. -/
theorem flatExponential_littleO_everyPower :
    Specs.SingleVariableAnalysis.Ch06.FlatDecay.littleOEveryPower := by
  intro m
  have hl : ScalarLittleO (𝓝[≠] (0 : ℝ)) flatExponential (fun x => |x| ^ m) := by
    apply (scalarLittleO_iff_ratio_tendsto _ _ _ ?_).mpr
    · apply (flatExponential_inversePower_decay m).congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := hx
      rw [flatExponential_of_ne_zero hx0]
      simp only [zpow_neg, zpow_natCast, div_eq_mul_inv]
      exact mul_comm _ _
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact pow_ne_zero _ (abs_ne_zero.mpr hx)
  change ScalarLittleO (𝓝 (0 : ℝ)) flatExponential (fun x => |x| ^ m)
  intro ε hε
  rw [← nhdsNE_sup_pure (0 : ℝ), eventually_sup]
  exact ⟨hl ε hε, by simp [flatExponential_zero, mul_nonneg hε.le]⟩

/-- All coefficients of the finite power expansions are zero, at every order. -/
theorem flatExponential_zeroPower_expansion :
    Specs.SingleVariableAnalysis.Ch06.FlatDecay.zeroPowerExpansion := by
  intro m
  simpa only [mul_zero, zero_mul, Finset.sum_const_zero, sub_zero] using
    flatExponential_littleO_everyPower m

end SingleVariableAnalysis
