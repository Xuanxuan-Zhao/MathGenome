import MathGenome.Internal.Specs.D05.Foundations.ComplexRoots
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue

/-! The root lemma preceding the manuscript's proof of FTA.
Positive real roots are obtained by IVT, then complex roots by polar form
and de Moivre's formula. -/

namespace D05.Foundations.ComplexRoots

/-- IVT on `[0, r + 1]` gives a positive real m-th root of positive r. -/
theorem positiveRealRoot (r : ℝ) (m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    ∃ s : ℝ, 0 < s ∧ s ^ m = r := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hbound : r ≤ (r + 1) ^ m :=
    (le_add_of_nonneg_right zero_le_one).trans
      (le_self_pow₀ (le_add_of_nonneg_left hr.le) hm0)
  have hmem : r ∈ Set.Icc ((0 : ℝ) ^ m) ((r + 1) ^ m) := by
    simpa only [Set.mem_Icc, zero_pow hm0] using And.intro hr.le hbound
  obtain ⟨s, hs, hpow⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ r + 1 from
      (hr.le.trans (le_add_of_nonneg_right zero_le_one)))
      (continuous_id.pow m).continuousOn hmem
  refine ⟨s, lt_of_le_of_ne hs.1 ?_, hpow⟩
  intro hzero
  have : r = 0 := by simpa [← hzero, zero_pow hm0] using hpow.symm
  exact hr.ne' this

/-- The zero case in the manuscript's proof. -/
theorem zeroRoot (m : ℕ) (hm : 0 < m) : (0 : ℂ) ^ m = 0 :=
  zero_pow (Nat.ne_of_gt hm)

/-- Construct an m-th root from a real root of the modulus and divided argument. -/
theorem complexRoot (z : ℂ) (m : ℕ) (hm : 0 < m) : ∃ w : ℂ, w ^ m = z := by
  by_cases hz : z = 0
  · exact ⟨0, by simpa only [hz] using zeroRoot m hm⟩
  obtain ⟨s, _, hs⟩ := positiveRealRoot ‖z‖ m (norm_pos_iff.mpr hz) hm
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hangle : (m : ℂ) * ((z.arg : ℂ) / (m : ℂ)) = (z.arg : ℂ) := by
    field_simp
  refine ⟨(s : ℂ) * (Complex.cos ((z.arg : ℂ) / (m : ℂ)) +
    Complex.sin ((z.arg : ℂ) / (m : ℂ)) * Complex.I), ?_⟩
  rw [mul_pow, ← Complex.ofReal_pow, hs, Complex.cos_add_sin_mul_I_pow, hangle]
  exact Complex.norm_mul_cos_add_sin_mul_I z

end D05.Foundations.ComplexRoots
