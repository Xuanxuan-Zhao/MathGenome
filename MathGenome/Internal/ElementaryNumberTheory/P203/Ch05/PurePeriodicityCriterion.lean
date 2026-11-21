import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.PurePeriodicityCriterion
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.LagrangePeriodicity
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.ReducedPredecessors

namespace P203
open P203Specs

/-- The canonical quotient map is injective on the reduced quadratics. -/
theorem reduced_step_injective (x y : ℝ) (hx : ReducedQuadratic x)
    (hy : ReducedQuadratic y) (heq : continuedFractionStep x = continuedFractionStep y) :
    x = y := by
  have hz := (reduced_step y hy).2.1
  have hu := (reduced_predecessor (continuedFractionStep y) hz).2.2.2.2.2
  exact (hu x hx heq).trans (hu y hy rfl).symm

/-- Every iterate of a reduced quadratic is still reduced. -/
theorem reduced_iterates (x : ℝ) (hx : ReducedQuadratic x) (n : ℕ) :
    ReducedQuadratic (continuedFractionStep^[n] x) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (reduced_step _ ih).2.1

/-- Uniqueness of reduced predecessors cancels any finite number of steps. -/
theorem reduced_iterate_injective (x y : ℝ) (hx : ReducedQuadratic x)
    (hy : ReducedQuadratic y) (n : ℕ)
    (heq : continuedFractionStep^[n] x = continuedFractionStep^[n] y) : x = y := by
  induction n with
  | zero => exact heq
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at heq
    exact ih (reduced_step_injective _ _ (reduced_iterates x hx n)
      (reduced_iterates y hy n) heq)

/-- A repeated pair of reduced orbit points pulls back to a return at zero. -/
theorem reduced_return_of_repeat (x : ℝ) (hx : ReducedQuadratic x)
    (i j : ℕ) (hij : i < j)
    (heq : continuedFractionStep^[j] x = continuedFractionStep^[i] x) :
    continuedFractionStep^[j - i] x = x := by
  apply reduced_iterate_injective _ _ (reduced_iterates x hx (j - i)) hx i
  rw [← Function.iterate_add_apply, Nat.add_sub_of_le hij.le]
  exact heq

/-- Reduction removes the entire preperiod, rather than just ensuring eventual
periodicity: equal tails give equal quotients, which cancel backwards. -/
theorem reduced_purely_periodic (x : ℝ) (hx : ReducedQuadratic x) :
    PurelyPeriodicCF x := by
  have hi := quadratic_is_irrational x hx.1
  obtain ⟨_, m, r, hr, hd⟩ :=
    (eventual_periodicity_bridge x).mp (quadratic_eventually_periodic x hx.1)
  have hrepeat : continuedFractionStep^[m + r] x = continuedFractionStep^[m] x := by
    apply infinite_digit_uniqueness _ _ (quotient_iterates x hi (m + r)).1
      (quotient_iterates x hi m).1
    intro n
    rw [partialQuotient_iterate x hi (m + r) n, partialQuotient_iterate x hi m n]
    rw [show m + r + n = (m + n) + r by omega]
    exact hd (m + n) (by omega)
  have hreturn : continuedFractionStep^[r] x = x := by
    have h := reduced_return_of_repeat x hx m (m + r) (by omega) hrepeat
    simpa only [Nat.add_sub_cancel_left] using h
  apply (pure_periodicity_bridge x).mpr
  refine ⟨hi, r, hr, ?_⟩
  intro n
  rw [(quotient_iterates x hi (n + r)).2.2, (quotient_iterates x hi n).2.2,
    Function.iterate_add_apply, hreturn]

/-- The canonical simple continued fraction of a real quadratic irrational is
purely periodic if and only if it is reduced, with strict conjugate bounds. -/
theorem pure_periodicity_criterion : P203Specs.PurePeriodicityCriterion := by
  intro x hx
  exact ⟨fun hp => (purely_periodic_quadratic_reduced x
    (quadratic_is_irrational x hx) hp).2, reduced_purely_periodic x⟩

end P203
