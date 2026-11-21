import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.DirichletBoundedDenominators
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace P203.Ch05.DirichletBoundedDenominators

/-- The finite bound in `paper.tex`, §nt:E05. -/
theorem boundedDenominators :
    P203Specs.Ch05.DirichletBoundedDenominators.BoundedDenominators := by
  intro x N hN
  have hN0 : 0 ≤ N := le_trans (by decide : (0 : ℤ) ≤ 1) hN
  have hcast : (N.toNat : ℤ) = N := Int.toNat_of_nonneg hN0
  have hpos : 0 < N.toNat := by omega
  obtain ⟨p, q, hq, hqN, herr⟩ := Real.exists_int_int_abs_mul_sub_le x hpos
  refine ⟨p, q, hq, ?_, ?_⟩
  · simpa only [hcast] using hqN
  · have hreal : (N.toNat : ℝ) = (N : ℝ) := by exact_mod_cast hcast
    simpa only [hreal] using herr

/-- Equality with the rational bound contradicts irrationality. -/
theorem strictBoundedDenominators :
    P203Specs.Ch05.DirichletBoundedDenominators.StrictBoundedDenominators := by
  intro x hx N hN
  obtain ⟨p, q, hq, hqN, herr⟩ := boundedDenominators x N hN
  refine ⟨p, q, hq, hqN, lt_of_le_of_ne herr ?_⟩
  intro heq
  have hi : Irrational ((q : ℝ) * x - (p : ℝ)) :=
    (hx.intCast_mul (by omega : q ≠ 0)).sub_intCast p
  have hrat : (((1 / ((N : ℚ) + 1)) : ℚ) : ℝ) = 1 / ((N : ℝ) + 1) := by
    norm_cast
  rcases eq_or_eq_neg_of_abs_eq heq with h | h
  · exact hi.ne_rat (1 / ((N : ℚ) + 1)) (h.trans hrat.symm)
  · exact hi.ne_rat (-(1 / ((N : ℚ) + 1))) (by simpa only [Rat.cast_neg, hrat] using h)

/-- Canonical rational numerators and denominators give the source's reduced pairs,
while the infinite set itself records distinct rational values. -/
theorem infiniteReducedApproximations :
    P203Specs.Ch05.DirichletBoundedDenominators.InfiniteReducedApproximations := by
  intro x hx
  apply (Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx).mono
  intro r hr
  change |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ 2 at hr
  refine ⟨r.num, (r.den : ℤ), ?_, ?_, ?_, ?_⟩
  · exact_mod_cast r.den_pos
  · simpa only [Int.gcd_def, Int.natAbs_natCast] using r.reduced.gcd_eq_one
  · simpa only [Int.cast_natCast] using r.num_div_den.symm
  · simpa only [Int.cast_natCast, ← Rat.cast_def] using hr

end P203.Ch05.DirichletBoundedDenominators
