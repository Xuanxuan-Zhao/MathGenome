import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.StandardLimits
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.PositiveRoots
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SequenceLimit
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Reference sequences without logarithms

The four conclusions of K03.01.standard_limits. Positive source indices are
represented by `n + 1`, consistently with the upstream sequence interface.

The library geometric limit uses Bernoulli's inequality and inversion. The
polynomial/geometric limit uses the finite-power continuity and Bernoulli
estimate in `isLittleO_pow_const_const_pow_of_one_lt`; neither argument uses
logarithms or exponentials. For the root limit, that estimate with `k = 1`
shows that eventually `n < (1 + ε)^n`. Taking the nonnegative integer root
traps the source root between `1` and `1 + ε`. Thus the root assertion concerns
exactly the upstream supremum construction and also needs no logarithms.
-/
namespace SingleVariableAnalysis

open Filter
open scoped Topology

theorem real_geometric_decay (q : ℝ) (hq : |q| < 1) :
    RealSequenceConverges (fun n => q ^ (n + 1)) 0 := by
  apply (realSequenceConverges_iff _ _).mpr
  exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).comp
    (tendsto_add_atTop_nat 1)

theorem complex_geometric_decay (q : ℂ) (hq : ‖q‖ < 1) :
    ComplexSequenceConverges (fun n => q ^ (n + 1)) 0 := by
  apply (complexSequenceConverges_iff _ _).mpr
  exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp
    (tendsto_add_atTop_nat 1)

theorem polynomial_over_geometric_decay (k : ℕ) (r : ℝ) (hr : 1 < r) :
    RealSequenceConverges (fun n => (n + 1 : ℝ) ^ k / r ^ (n + 1)) 0 := by
  apply (realSequenceConverges_iff _ _).mpr
  simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
    (tendsto_pow_const_div_const_pow_of_one_lt k hr).comp (tendsto_add_atTop_nat 1)

theorem integer_root_self_limit :
    RealSequenceConverges (fun n => nonnegativeRoot (n + 1) (n + 1 : ℕ)) 1 := by
  intro ε hε
  have hr : 1 < 1 + ε := by linarith
  obtain ⟨N, hN⟩ := polynomial_over_geometric_decay 1 (1 + ε) hr 1 zero_lt_one
  refine ⟨N, fun n hn => ?_⟩
  change |nonnegativeRoot (n + 1) (n + 1 : ℕ) - 1| < ε
  have hd : 0 < n + 1 := Nat.succ_pos n
  have hb : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hd
  have hnonneg := nonnegativeRoot_nonneg (n + 1) hd (n + 1 : ℕ) (by positivity)
  have hpow := nonnegativeRoot_pow (n + 1) hd (n + 1 : ℕ) (by positivity)
  have hl : 1 ≤ nonnegativeRoot (n + 1) (n + 1 : ℕ) := by
    apply (pow_le_pow_iff_left₀ zero_le_one hnonneg (Nat.ne_of_gt hd)).mp
    simpa only [one_pow, hpow] using hb
  have hratio : (n + 1 : ℝ) / (1 + ε) ^ (n + 1) < 1 := by
    have := (abs_lt.mp (hN n hn)).2
    simpa only [pow_one, sub_zero] using this
  have hbase : 0 < 1 + ε := by linarith
  have hlarge : (n + 1 : ℝ) < (1 + ε) ^ (n + 1) :=
    (div_lt_one (pow_pos hbase _)).mp hratio
  have hu : nonnegativeRoot (n + 1) (n + 1 : ℕ) < 1 + ε := by
    apply (pow_lt_pow_iff_left₀ hnonneg hbase.le (Nat.ne_of_gt hd)).mp
    rw [hpow]
    simpa only [Nat.cast_add, Nat.cast_one] using hlarge
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  linarith

end SingleVariableAnalysis
