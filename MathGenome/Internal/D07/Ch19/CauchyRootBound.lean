import MathGenome.Internal.Specs.D07.Ch19.CauchyRootBound
import MathGenome.Internal.D07.Ch11.EvaluationUniversal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Order.GroupWithZero.Finset

/-!
Cauchy's strict bound for each complex root (K07.19.cauchy_root_bound).
The library bound is identified with the maximum of the normalized lower
coefficients in the independent specification. Its proof uses evaluation,
the triangle inequality, and a finite geometric sum; it does not use FTA.
-/

namespace D07.Ch19.CauchyRootBound

open Polynomial
open scoped NNReal
open Specs.D07.Ch19.CauchyRootBound

/-- Dividing the maximum coefficient norm by the leading coefficient norm
is exactly the maximum of the normalized coefficient norms. -/
theorem cauchyBound_eq (f : Polynomial ℂ) :
    f.cauchyBound = normalizedCoefficientMaximum f + 1 := by
  unfold Polynomial.cauchyBound normalizedCoefficientMaximum
  rw [Finset.sup_div₀ zero_le]
  simp only [nnnorm_div]

theorem maximumCharacterization : MaximumCharacterization := by
  intro f hn
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (Finset.range f.natDegree)
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)) (fun i => ‖f.coeff i / f.leadingCoeff‖₊)
  constructor
  · exact ⟨i, Finset.mem_range.mp hi, congrArg (fun r : ℝ≥0 => (r : ℝ)) heq⟩
  · rintro r ⟨j, hj, rfl⟩
    exact_mod_cast (Finset.le_sup (f := fun i => ‖f.coeff i / f.leadingCoeff‖₊)
      (Finset.mem_range.mpr hj))

theorem rootBound : RootBound := by
  intro f hn z hz
  have hf : f ≠ 0 := by
    intro h
    simp [h] at hn
  have h := hz.norm_lt_cauchyBound hf
  rw [cauchyBound_eq] at h
  have h' : ‖z‖ < (normalizedCoefficientMaximum f : ℝ) + 1 := by
    exact_mod_cast h
  simpa only [add_comm] using h'

theorem zeroMaximumRoot : ZeroMaximumRoot := by
  intro f hn hM z hz
  have hf : f ≠ 0 := by
    intro h
    simp [h] at hn
  have hcoeff : ∀ i, i < f.natDegree → f.coeff i = 0 := by
    intro i hi
    have hle := Finset.le_sup (f := fun i => ‖f.coeff i / f.leadingCoeff‖₊)
      (Finset.mem_range.mpr hi)
    change ‖f.coeff i / f.leadingCoeff‖₊ ≤ normalizedCoefficientMaximum f at hle
    rw [hM] at hle
    have hdiv : f.coeff i / f.leadingCoeff = 0 := by
      simpa using (le_antisymm hle zero_le)
    exact (div_eq_zero_iff.mp hdiv).resolve_right (leadingCoeff_ne_zero.mpr hf)
  have heval : f.eval z = f.leadingCoeff * z ^ f.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
    simp only [coeff_natDegree]
    rw [Finset.sum_eq_zero (fun i hi => by rw [hcoeff i (Finset.mem_range.mp hi), zero_mul]),
      zero_add]
  have hpow : z ^ f.natDegree = 0 := by
    have hzero : f.leadingCoeff * z ^ f.natDegree = 0 := heval.symm.trans hz
    exact (mul_eq_zero.mp hzero).resolve_left (leadingCoeff_ne_zero.mpr hf)
  exact eq_zero_of_pow_eq_zero hpow

end D07.Ch19.CauchyRootBound
