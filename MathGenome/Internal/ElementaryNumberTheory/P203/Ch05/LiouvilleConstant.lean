import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.LiouvilleConstant
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.Localization.Integral

noncomputable section

namespace P203

/-- The exact source constant `∑_{j=1}^∞ 10^{-j!}`. -/
def liouvilleConstant : ℝ :=
  ∑' n : ℕ, 1 / (10 : ℝ) ^ (n + 1).factorial

/-- The factorial series starting at `1!` converges. -/
theorem liouvilleConstant_summable : P203Specs.LiouvilleConstantSummable := by
  exact (summable_nat_add_iff 1).2 (LiouvilleNumber.summable (by norm_num : (1 : ℝ) < 10))

/-- Convergence identifies the constant with the sum of its defining series. -/
theorem liouvilleConstant_hasSum : P203Specs.LiouvilleConstantHasSum :=
  liouvilleConstant_summable.hasSum

/-- Mathlib includes the `0!` term, which contributes exactly `1/10`. -/
theorem liouvilleNumber_ten_eq : liouvilleNumber 10 = liouvilleConstant + 1 / 10 := by
  have h := (LiouvilleNumber.summable (by norm_num : (1 : ℝ) < 10)).tsum_eq_zero_add
  simpa only [liouvilleNumber, liouvilleConstant, Nat.factorial_zero, pow_one, add_comm] using h

/-- Translation by a rational preserves transcendence over the rationals. -/
theorem transcendental_add_rat_iff (x : ℝ) (r : ℚ) :
    Transcendental ℚ (x + (r : ℝ)) ↔ Transcendental ℚ x := by
  constructor
  · intro h hx
    exact h (hx.add (isAlgebraic_ratCast ℚ r))
  · intro h hx
    apply h
    have hs := hx.sub (isAlgebraic_ratCast ℚ r)
    simpa only [add_sub_cancel_right] using hs

/-- Liouville's theorem applies to the library constant; the exact rational
translation transfers transcendence to the source's series. -/
theorem liouvilleConstant_transcendental : P203Specs.LiouvilleConstantTranscendental := by
  have htZ := transcendental_liouvilleNumber (m := 10) (by norm_num)
  have htQ : Transcendental ℚ (liouvilleNumber 10) := by
    intro h
    exact htZ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr h)
  rw [liouvilleNumber_ten_eq] at htQ
  exact (transcendental_add_rat_iff liouvilleConstant (1 / 10)).mp (by simpa using htQ)

/-- In particular, the source constant is irrational. -/
theorem liouvilleConstant_irrational : P203Specs.LiouvilleConstantIrrational :=
  liouvilleConstant_transcendental.irrational

end P203
