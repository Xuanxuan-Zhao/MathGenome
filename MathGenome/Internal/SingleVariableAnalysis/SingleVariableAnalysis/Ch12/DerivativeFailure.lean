import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.SinCos
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.PiPeriod
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Chain
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.SupNorm
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.DerivativeFailure

/-!
# Uniform convergence does not control derivatives

K03.12.derivative_failure, paper.tex:1334–1339. The term at Lean index `n`
is the source term at positive index `n + 1`. Its absolute value, and hence
its extended supremum error on the whole line, is at most `1 / (n + 1)`.
The chain rule and division by this nonzero constant give its derivative.
At pi, two arbitrarily late terms have values -1 and 1, excluding any limit.
The canonical functions used here are the constructed series and analytic pi
by `sinCosSeries_eq_real` and `analyticPi_eq_pi` in the imported prerequisites.
-/

noncomputable section
namespace SingleVariableAnalysis

/-- The positive-indexed family `sin(k*x)/k`, with `k = n + 1`. -/
def sineQuotient (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n + 1 : ℕ) * x) / (n + 1 : ℕ)

theorem sineQuotient_bound (n : ℕ) (x : ℝ) :
    |sineQuotient n x| ≤ 1 / (n + 1 : ℕ) := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  simpa only [sineQuotient, abs_div, abs_of_pos hn] using
    (div_le_div_of_nonneg_right (Real.abs_sin_le_one ((n + 1 : ℕ) * x)) hn.le)

theorem sineQuotient_supError_bound (n : ℕ) :
    realSupError sineQuotient (fun _ => 0) n ≤
      ENNReal.ofReal (1 / (n + 1 : ℕ)) := by
  apply iSup_le
  intro x
  simpa only [sub_zero] using ENNReal.ofReal_le_ofReal (sineQuotient_bound n x)

theorem sineQuotient_uniform :
    RealUniformConverges sineQuotient (fun _ => 0) := by
  intro ε hε
  obtain ⟨N, _, hN⟩ := reciprocal_tail ε hε
  refine ⟨N, fun n hn x => ?_⟩
  simpa only [sub_zero] using
    (sineQuotient_bound n x).trans_lt
      (lt_of_le_of_lt (le_abs_self _) (hN (n + 1) (by omega)))

theorem sineQuotient_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (sineQuotient n) (Real.cos ((n + 1 : ℕ) * x)) x := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  convert ((Real.hasDerivAt_sin ((n + 1 : ℕ) * x)).comp x
    (hasDerivAt_const_mul ((n + 1 : ℕ) : ℝ))).div_const ((n + 1 : ℕ) : ℝ) using 1
  · rfl
  · exact (mul_div_cancel_right₀ _ hn).symm

theorem sineQuotient_deriv_pi (n : ℕ) :
    deriv (sineQuotient n) Real.pi = (-1 : ℝ) ^ (n + 1) := by
  rw [(sineQuotient_hasDerivAt n Real.pi).deriv, Real.cos_nat_mul_pi]

theorem sineQuotient_deriv_not_convergent (L : ℝ) :
    ¬ RealSequenceConverges (fun n => deriv (sineQuotient n) Real.pi) L := by
  intro h
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  have hneg := hN (2 * N) (by omega)
  have hpos := hN (2 * N + 1) (by omega)
  dsimp only at hneg hpos
  rw [sineQuotient_deriv_pi] at hneg hpos
  norm_num [pow_add, pow_mul] at hneg hpos
  have h₁ := (abs_lt.mp hneg).1
  have h₂ := (abs_lt.mp hpos).2
  linarith

theorem sineQuotient_deriv_not_pointwise :
    ¬ ∃ g : ℝ → ℝ, RealPointwiseConverges
      (fun n x => deriv (sineQuotient n) x) g := by
  rintro ⟨g, hg⟩
  exact sineQuotient_deriv_not_convergent (g Real.pi) (hg Real.pi)

end SingleVariableAnalysis
