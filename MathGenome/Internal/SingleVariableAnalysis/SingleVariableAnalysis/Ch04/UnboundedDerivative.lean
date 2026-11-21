import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.UnboundedDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! The derivative at zero follows from the manuscript's quotient estimate.
Elsewhere the product and chain rules apply. The explicit positive sequence
tends to zero while its derivative tends to minus infinity. -/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped Topology

def unboundedDerivativeExample : ℝ → ℝ :=
  fun x => if x = 0 then 0 else x ^ 2 * Real.sin (1 / x ^ 2)

def unboundedDerivativeSequence (n : ℕ) : ℝ := 1 / Real.sqrt (2 * Real.pi * n)

private theorem example_eq (x : ℝ) :
    unboundedDerivativeExample x = x ^ 2 * Real.sin (1 / x ^ 2) := by
  by_cases hx : x = 0 <;> simp [unboundedDerivativeExample, hx]

theorem unboundedDerivative_hasDerivAt_zero : HasDerivAt unboundedDerivativeExample 0 0 := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp
  rw [realDerivative_epsilon_iff]
  intro ε hε
  refine ⟨ε, hε, fun h hp hh => ?_⟩
  have hn : h ≠ 0 := abs_pos.mp hp
  have he : (unboundedDerivativeExample (0 + h) - unboundedDerivativeExample 0) / h - 0 =
      h * Real.sin (1 / h ^ 2) := by
    simp only [zero_add, example_eq, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero]
    field_simp
  rw [he, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg h) (Real.abs_sin_le_one _)).trans_lt hh

theorem unboundedDerivative_hasDerivAt_nonzero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt unboundedDerivativeExample
      (2 * x * Real.sin (1 / x ^ 2) - (2 / x) * Real.cos (1 / x ^ 2)) x := by
  have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> first | rfl | norm_num
  have hi : HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-(2 * x) / (x ^ 2) ^ 2) x := by
    convert hp.inv (pow_ne_zero 2 hx) using 1
    ext y
    simp only [Pi.inv_apply, one_div]
  have hd := hp.mul ((Real.hasDerivAt_sin (1 / x ^ 2)).comp x hi)
  convert hd using 1
  · exact funext example_eq
  · dsimp only [Function.comp_apply]
    field_simp
    ring

theorem unboundedDerivative_differentiable : Differentiable ℝ unboundedDerivativeExample := by
  intro x
  by_cases hx : x = 0
  · subst x; exact unboundedDerivative_hasDerivAt_zero.differentiableAt
  · exact (unboundedDerivative_hasDerivAt_nonzero x hx).differentiableAt

theorem unboundedDerivative_deriv_zero : deriv unboundedDerivativeExample 0 = 0 :=
  unboundedDerivative_hasDerivAt_zero.deriv

theorem unboundedDerivative_deriv_nonzero (x : ℝ) (hx : x ≠ 0) :
    deriv unboundedDerivativeExample x =
      2 * x * Real.sin (1 / x ^ 2) - (2 / x) * Real.cos (1 / x ^ 2) :=
  (unboundedDerivative_hasDerivAt_nonzero x hx).deriv

theorem unboundedDerivativeSequence_pos (n : ℕ) (hn : 0 < n) :
    0 < unboundedDerivativeSequence n := by
  unfold unboundedDerivativeSequence
  positivity

private theorem sqrt_sequence_tendsto :
    Tendsto (fun n : ℕ => Real.sqrt (2 * Real.pi * n)) atTop atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)

theorem unboundedDerivativeSequence_tendsto_zero :
    Tendsto unboundedDerivativeSequence atTop (𝓝 0) := by
  unfold unboundedDerivativeSequence
  simpa only [one_div, Function.comp_def] using
    tendsto_inv_atTop_zero.comp sqrt_sequence_tendsto

theorem unboundedDerivative_deriv_sequence (n : ℕ) (hn : 0 < n) :
    deriv unboundedDerivativeExample (unboundedDerivativeSequence n) =
      -2 * Real.sqrt (2 * Real.pi * n) := by
  have hp : 0 < 2 * Real.pi * (n : ℝ) := by positivity
  have ha : 1 / unboundedDerivativeSequence n ^ 2 = (n : ℝ) * (2 * Real.pi) := by
    rw [unboundedDerivativeSequence, div_pow, one_pow, one_div_one_div,
      Real.sq_sqrt hp.le]
    ring
  rw [unboundedDerivative_deriv_nonzero _ (ne_of_gt (unboundedDerivativeSequence_pos n hn)), ha]
  have hsin : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    simpa only [zero_add, Real.sin_zero] using Real.sin_add_nat_mul_two_pi 0 n
  rw [hsin, Real.cos_nat_mul_two_pi, mul_zero, zero_sub, mul_one]
  simp only [unboundedDerivativeSequence, one_div, div_inv_eq_mul]
  ring

theorem unboundedDerivative_deriv_sequence_tendsto :
    Tendsto (fun n => deriv unboundedDerivativeExample (unboundedDerivativeSequence n))
      atTop atBot := by
  have ht : Tendsto (fun n : ℕ => -2 * Real.sqrt (2 * Real.pi * n)) atTop atBot := by
    simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp
      (sqrt_sequence_tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (unboundedDerivative_deriv_sequence n hn).symm

theorem unboundedDerivative_locally_unbounded_below (δ : ℝ) (hδ : 0 < δ) (B : ℝ) :
    ∃ x : ℝ, 0 < x ∧ x < δ ∧ deriv unboundedDerivativeExample x < B := by
  have hs := unboundedDerivativeSequence_tendsto_zero.eventually (gt_mem_nhds hδ)
  have hd := unboundedDerivative_deriv_sequence_tendsto.eventually (eventually_lt_atBot B)
  obtain ⟨n, hn, hns, hnd⟩ :=
    ((eventually_gt_atTop 0).and (hs.and hd)).exists
  exact ⟨_, unboundedDerivativeSequence_pos n hn, hns, hnd⟩

theorem unboundedDerivative_locally_unbounded (δ : ℝ) (hδ : 0 < δ) (M : ℝ) :
    ∃ x : ℝ, 0 < |x| ∧ |x| < δ ∧ M < |deriv unboundedDerivativeExample x| := by
  obtain ⟨x, hx, hxd, hd⟩ := unboundedDerivative_locally_unbounded_below δ hδ (-M)
  refine ⟨x, by simpa [abs_of_pos hx] using hx, by simpa [abs_of_pos hx] using hxd, ?_⟩
  simpa only [neg_neg] using (neg_lt_neg hd).trans_le (neg_le_abs _)

end SingleVariableAnalysis
