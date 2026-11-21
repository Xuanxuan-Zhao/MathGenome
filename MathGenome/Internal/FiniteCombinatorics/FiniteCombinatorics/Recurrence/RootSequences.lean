import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.RootSequences
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

noncomputable section
universe u
namespace FiniteCombinatorics.Recurrence

/-- The coefficient sequence of `z^j/(1 - λz)^(j+1)`. -/
def rootSequence {K : Type u} [Field K] (lam : K) (j n : ℕ) : K :=
  PowerSeries.coeff n ((PowerSeries.X : PowerSeries K) ^ j *
    ((1 - PowerSeries.C lam * PowerSeries.X) ^ (j + 1))⁻¹)

/-- The left shift on sequences. -/
def leftShift {K : Type u} [Field K] : Module.End K (ℕ → K) where
  toFun a n := a (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem denominator_inverse {K : Type u} [Field K] (lam : K) (j : ℕ) :
    ((1 - PowerSeries.C lam * PowerSeries.X : PowerSeries K) ^ (j + 1))⁻¹ =
      PowerSeries.rescale lam (PowerSeries.mk fun n => (Nat.choose (j + n) j : K)) := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).mpr
  have h := congrArg (PowerSeries.rescale lam)
    (PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one K j)
  simpa only [map_mul, map_pow, map_sub, map_one, PowerSeries.rescale_X] using h

theorem rootSequence_coeff {K : Type u} [Field K] (lam : K) (j n : ℕ) :
    rootSequence lam j n =
      if j ≤ n then (Nat.choose n j : K) * lam ^ (n - j) else 0 := by
  rw [rootSequence, denominator_inverse, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
      Nat.add_sub_of_le h, mul_comm]
  · rfl

private theorem rootSequence_eq_choose {K : Type u} [Field K] (lam : K) (j n : ℕ) :
    rootSequence lam j n = (Nat.choose n j : K) * lam ^ (n - j) := by
  rw [rootSequence_coeff]
  split_ifs with h
  · rfl
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

theorem rootSequence_zero {K : Type u} [Field K] (j n : ℕ) :
    rootSequence (0 : K) j n = if n = j then 1 else 0 := by
  simp [rootSequence, PowerSeries.coeff_X_pow]

theorem shift_root_zero {K : Type u} [Field K] (lam : K) :
    (leftShift (K := K) - lam • (LinearMap.id : Module.End K (ℕ → K))) (rootSequence lam 0) = 0 := by
  funext n
  change rootSequence lam 0 (n + 1) - lam * rootSequence lam 0 n = 0
  simp only [rootSequence_eq_choose, Nat.choose_zero_right, Nat.cast_one,
    one_mul, Nat.sub_zero, pow_succ]
  ring

theorem shift_root_succ {K : Type u} [Field K] (lam : K) (j : ℕ) :
    (leftShift (K := K) - lam • (LinearMap.id : Module.End K (ℕ → K))) (rootSequence lam (j + 1)) =
      rootSequence lam j := by
  funext n
  change rootSequence lam (j + 1) (n + 1) -
    lam * rootSequence lam (j + 1) n = rootSequence lam j n
  by_cases h : j ≤ n
  · by_cases heq : j = n
    · subst j
      simp [rootSequence_eq_choose]
    · have hexp : n - j = n - (j + 1) + 1 := by omega
      rw [rootSequence_eq_choose, rootSequence_eq_choose, rootSequence_eq_choose,
        Nat.choose_succ_succ, Nat.cast_add,
        show n + 1 - (j + 1) = n - j by omega]
      rw [hexp, pow_succ]
      ring
  · have hlt : n < j := by omega
    simp [rootSequence_eq_choose,
      Nat.choose_eq_zero_of_lt hlt,
      Nat.choose_eq_zero_of_lt (show n < j + 1 by omega),
      Nat.choose_eq_zero_of_lt (show n + 1 < j + 1 by omega)]

theorem rootSequence_annihilation {K : Type u} [Field K] (lam : K) (j : ℕ) :
    ((leftShift (K := K) - lam • (LinearMap.id : Module.End K (ℕ → K))) ^ (j + 1)) (rootSequence lam j) = 0 := by
  induction j with
  | zero => simpa using shift_root_zero lam
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, shift_root_succ, ih]

end FiniteCombinatorics.Recurrence
