import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.QuadraticPrimitives
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.ElementaryPrimitives
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Quadratic primitives for K03.09.partial_fractions, paper.tex:2685–2700.
With q = y² + d and m = k − 1, differentiating y/q^m gives
2md/q^(m+1) − (2m−1)/q^m. Dividing by 2md and adding the
previous primitive with coefficient (2m−1)/(2md) cancels the second
term. The scaled arctangent starts the induction. Positivity of d
supplies every nonzero denominator, for every real argument.
-/
noncomputable section
namespace SingleVariableAnalysis.QuadraticPrimitives
open Specs.SingleVariableAnalysis.Ch09.QuadraticPrimitives

def quadraticPrimitive : ℝ → ℕ → ℝ → ℝ := quadraticPrimitiveValue

theorem quadratic_primitive_base : quadraticPrimitiveBase := by
  intro d y _
  rfl

theorem quadratic_primitive_recurrence : quadraticPrimitiveRecurrence := by
  intro d k _ hk y
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hn : 2 + n - 1 = n + 1 := by omega
  have ha : ((2 + n : ℕ) : ℝ) - 1 = (n : ℝ) + 1 := by push_cast; ring
  have hb : 2 * ((2 + n : ℕ) : ℝ) - 3 = 2 * (n : ℝ) + 1 := by push_cast; ring
  rw [hn, ha, hb, Nat.add_comm 2 n]
  rfl

private theorem base_hasDerivAt (d : ℝ) (hd : 0 < d) (y : ℝ) :
    HasDerivAt (quadraticPrimitive d 1) (1 / (y ^ 2 + d)) y := by
  have hs : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have h := ((Real.hasDerivAt_arctan (y / Real.sqrt d)).comp y
    ((hasDerivAt_id y).div_const (Real.sqrt d))).const_mul (Real.sqrt d)⁻¹
  convert h using 1
  · rfl
  · field_simp
    nlinarith [sq_nonneg y]

private theorem reduction_hasDerivAt (d : ℝ) (hd : 0 < d) (n : ℕ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => t / (t ^ 2 + d) ^ (n + 1))
      (2 * ((n : ℝ) + 1) * d / (y ^ 2 + d) ^ (n + 2) -
        (2 * (n : ℝ) + 1) / (y ^ 2 + d) ^ (n + 1)) y := by
  have hq : y ^ 2 + d ≠ 0 := ne_of_gt (by positivity)
  have hp : (y ^ 2 + d) ^ n ≠ 0 := pow_ne_zero _ hq
  have h := (hasDerivAt_id y).div
    (((hasDerivAt_pow 2 y).add_const d).pow (n + 1)) (pow_ne_zero _ hq)
  change HasDerivAt (fun t : ℝ => t / (t ^ 2 + d) ^ (n + 1))
    ((1 * (y ^ 2 + d) ^ (n + 1) -
      y * ((n + 1 : ℕ) * (y ^ 2 + d) ^ (n + 1 - 1) * (2 * y ^ (2 - 1)))) /
      ((y ^ 2 + d) ^ (n + 1)) ^ 2) y at h
  apply h.congr_deriv
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ,
    one_mul]
  field_simp [hq, hp]
  ring

theorem quadratic_reduction_derivative : quadraticReductionDerivative := by
  intro d k hd hk y
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hn : 2 + n - 1 = n + 1 := by omega
  have ha : ((2 + n : ℕ) : ℝ) - 1 = (n : ℝ) + 1 := by push_cast; ring
  have hb : 2 * ((2 + n : ℕ) : ℝ) - 3 = 2 * (n : ℝ) + 1 := by push_cast; ring
  rw [hn, ha, hb, Nat.add_comm 2 n]
  exact reduction_hasDerivAt d hd n y

private theorem recurrence_step (d : ℝ) (hd : 0 < d) (n : ℕ)
    (J : ℝ → ℝ) (y : ℝ) (hJ : HasDerivAt J (1 / (y ^ 2 + d) ^ (n + 1)) y) :
    HasDerivAt (fun t : ℝ =>
      t / (2 * ((n : ℝ) + 1) * d * (t ^ 2 + d) ^ (n + 1)) +
        (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1) * d) * J t)
      (1 / (y ^ 2 + d) ^ (n + 2)) y := by
  have hc : 2 * ((n : ℝ) + 1) * d ≠ 0 := ne_of_gt (by positivity)
  have hq : y ^ 2 + d ≠ 0 := ne_of_gt (by positivity)
  have h := ((reduction_hasDerivAt d hd n y).div_const
    (2 * ((n : ℝ) + 1) * d)).add
    (hJ.const_mul ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1) * d)))
  convert h using 1
  · funext t
    change t / (2 * ((n : ℝ) + 1) * d * (t ^ 2 + d) ^ (n + 1)) +
      (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1) * d) * J t =
      t / (t ^ 2 + d) ^ (n + 1) / (2 * ((n : ℝ) + 1) * d) +
      (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1) * d) * J t
    rw [div_div, mul_comm ((t ^ 2 + d) ^ (n + 1))]
  · field_simp [hc, hq]
    ring

theorem quadratic_recurrence_step : quadraticRecurrenceStep := by
  intro d k hd hk J y hJ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hn : 2 + n - 1 = n + 1 := by omega
  have ha : ((2 + n : ℕ) : ℝ) - 1 = (n : ℝ) + 1 := by push_cast; ring
  have hb : 2 * ((2 + n : ℕ) : ℝ) - 3 = 2 * (n : ℝ) + 1 := by push_cast; ring
  rw [hn] at hJ
  rw [hn, ha, hb, Nat.add_comm 2 n]
  exact recurrence_step d hd n J y hJ

theorem quadratic_primitive_hasDerivAt : quadraticPrimitiveHasDerivAt := by
  intro d k hd hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h : ∀ n : ℕ, ∀ y : ℝ,
      HasDerivAt (quadraticPrimitive d (n + 1)) (1 / (y ^ 2 + d) ^ (n + 1)) y := by
    intro n
    induction n with
    | zero => simpa only [Nat.zero_add, pow_one] using base_hasDerivAt d hd
    | succ n ih =>
      intro y
      exact recurrence_step d hd n _ y (ih y)
  simpa only [quadraticPrimitive, Nat.add_comm 1 n] using h n

theorem quadratic_primitive_formula : quadraticPrimitiveFormula := by
  intro d k hd hk
  apply ElementaryPrimitives.formulaOn_of_hasDerivAt
  intro y _
  exact quadratic_primitive_hasDerivAt d k hd hk y

end SingleVariableAnalysis.QuadraticPrimitives
