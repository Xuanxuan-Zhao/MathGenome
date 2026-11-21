import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.TentQuotients
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.StandardLimits
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.NowhereDifferentiable

/-! The final limiting argument for the exact periodic-tent series of
K03.16.nowhere_differentiable (paper.tex:3958–3998). Continuity and the finite
quotient estimates are upstream. We choose the signed increments, prove their
limit and the divergence of quotient magnitudes, and contradict the local
boundedness required by a finite derivative. No series is differentiated. -/

noncomputable section
namespace SingleVariableAnalysis

open Filter
open scoped Topology

/-- A name for the counterexample reusing the canonical tent series. -/
def nowhereDifferentiableExample : ℝ → ℝ := tentSeries

theorem tentSeries_small_increments :
    Specs.SingleVariableAnalysis.Ch16.NowhereDifferentiable.tentSeriesSmallIncrements := by
  intro x
  have hw (m : ℕ) : ∃ h : ℝ,
      (h = (1 / 2 : ℝ) / 4 ^ (m + 1) ∨ h = -((1 / 2 : ℝ) / 4 ^ (m + 1))) ∧
      h ≠ 0 ∧ ((3 : ℝ) ^ (m + 1) + 1) / 2 ≤
        |(tentSeries (x + h) - tentSeries x) / h| := by
    obtain ⟨h, hs, hn, _, _, _, _, _, hb⟩ := tent_half_cell_quotients x (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m))
    exact ⟨h, hs, hn, hb⟩
  choose h hs hn hb using hw
  have habs (m : ℕ) : |h m| = (1 / 2 : ℝ) / 4 ^ (m + 1) := by
    rcases hs m with hm | hm <;> rw [hm]
    · exact abs_of_pos (div_pos (by norm_num) (pow_pos (by norm_num) _))
    · rw [abs_neg]
      exact abs_of_pos (div_pos (by norm_num) (pow_pos (by norm_num) _))
  have hfour : Tendsto (fun m : ℕ => (4 : ℝ) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).comp
      (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto h atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    simpa only [Function.comp_def, habs] using hfour.const_div_atTop (1 / 2 : ℝ)
  have hthree : Tendsto (fun m : ℕ => (3 : ℝ) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).comp
      (tendsto_add_atTop_nat 1)
  have hlarge : Tendsto (fun m : ℕ => ((3 : ℝ) ^ (m + 1) + 1) / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
      (tendsto_atTop_add_const_right atTop 1 hthree)
  exact ⟨h, hs, hn, hsmall, hb, tendsto_atTop_mono hb hlarge⟩

theorem tentSeries_no_finite_derivative (x L : ℝ) :
    ¬ HasRealIncrementDerivative tentSeries L x := by
  intro hd
  obtain ⟨h, _, hn, hz, _, hq⟩ := tentSeries_small_increments x
  obtain ⟨δ, hδ, hlocal⟩ := (realDerivative_epsilon_iff tentSeries L x).mp hd 1
    (by norm_num)
  have hnear : ∀ᶠ m in atTop, |h m| < δ := by
    have ha := ((tendsto_zero_iff_abs_tendsto_zero _).mp hz).eventually
      (gt_mem_nhds hδ)
    exact ha
  have hfar : ∀ᶠ m in atTop,
      |L| + 1 < |(tentSeries (x + h m) - tentSeries x) / h m| :=
    hq.eventually (eventually_gt_atTop (|L| + 1))
  obtain ⟨m, hmnear, hmfar⟩ := (hnear.and hfar).exists
  have he := hlocal (h m) (abs_pos.mpr (hn m)) hmnear
  have ht := abs_add_le ((tentSeries (x + h m) - tentSeries x) / h m - L) L
  rw [sub_add_cancel] at ht
  linarith

theorem tentSeries_not_differentiable (x : ℝ) :
    ¬ DifferentiableAt ℝ tentSeries x := by
  intro hd
  exact tentSeries_no_finite_derivative x (deriv tentSeries x)
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr hd.hasDerivAt)

theorem tentSeries_continuous_nowhere_differentiable :
    Continuous tentSeries ∧ ∀ x : ℝ, ¬ DifferentiableAt ℝ tentSeries x :=
  ⟨tentSeries_continuous, tentSeries_not_differentiable⟩

end SingleVariableAnalysis
