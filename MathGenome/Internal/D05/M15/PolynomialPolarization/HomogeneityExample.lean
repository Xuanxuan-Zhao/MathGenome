import MathGenome.Internal.Specs.D05.M15.PolynomialPolarization.HomogeneityExample
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The homogeneous, nonpolynomial real-plane example from paper.tex:3226–3228. -/

noncomputable section

namespace D05.M15.PolynomialPolarization.HomogeneityExample

open D05.Foundations

/-- The paper's piecewise-defined real-plane function. -/
def q : D05.Specs.PolynomialPolarization.HomogeneityExample.qType :=
  D05.Specs.PolynomialPolarization.HomogeneityExample.qValue

theorem formula : D05.Specs.PolynomialPolarization.HomogeneityExample.formula := by
  intro v
  by_cases h : v = 0
  · subst v
    simp [D05.Specs.PolynomialPolarization.HomogeneityExample.qValue]
  · simp [D05.Specs.PolynomialPolarization.HomogeneityExample.qValue, h]

theorem atOrigin : D05.Specs.PolynomialPolarization.HomogeneityExample.atOrigin := by
  simp [D05.Specs.PolynomialPolarization.HomogeneityExample.atOrigin,
    D05.Specs.PolynomialPolarization.HomogeneityExample.qValue]

private theorem zero_coordinates_of_denominator_zero (v : CoordinateModule ℝ 2)
    (h : v 0 ^ 2 + v 1 ^ 2 = 0) : v 0 = 0 ∧ v 1 = 0 := by
  constructor <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem homogeneity : D05.Specs.PolynomialPolarization.HomogeneityExample.homogeneity := by
  intro t v
  rw [formula, formula]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases ht : t = 0
  · simp [ht]
  by_cases hd : v 0 ^ 2 + v 1 ^ 2 = 0
  · obtain ⟨hx, hy⟩ := zero_coordinates_of_denominator_zero v hd
    simp [hx, hy]
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht
  have hscaled : (t * v 0) ^ 2 + (t * v 1) ^ 2 =
      t ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by ring
  rw [hscaled]
  field_simp

theorem sampleValues : D05.Specs.PolynomialPolarization.HomogeneityExample.sampleValues := by
  unfold D05.Specs.PolynomialPolarization.HomogeneityExample.sampleValues
  rw [formula, formula, formula, formula]
  norm_num

theorem notQuadraticExpression :
    D05.Specs.PolynomialPolarization.HomogeneityExample.notQuadraticExpression := by
  rintro ⟨a, b, c, h⟩
  have h10 := h ![1, 0]
  have h01 := h ![0, 1]
  have h11 := h ![1, 1]
  have h1n := h ![1, -1]
  obtain ⟨q10, q01, q11, q1n⟩ := sampleValues
  rw [q10] at h10
  rw [q01] at h01
  rw [q11] at h11
  rw [q1n] at h1n
  norm_num at h10 h01 h11 h1n
  linarith

/-- Clear the rational function's denominator, including at its zero. -/
private theorem multiply_denominator (v : CoordinateModule ℝ 2) :
    D05.Specs.PolynomialPolarization.HomogeneityExample.qValue v * (v 0 ^ 2 + v 1 ^ 2) = v 0 ^ 4 := by
  rw [formula]
  by_cases hd : v 0 ^ 2 + v 1 ^ 2 = 0
  · obtain ⟨hx, hy⟩ := zero_coordinates_of_denominator_zero v hd
    simp [hx, hy]
  · exact div_mul_cancel₀ _ hd

/-- Equality of real polynomial functions forces a formal identity. Evaluating
that identity at the complex point (i,1) contradicts i² + 1 = 0 and i⁴ = 1. -/
theorem notPolynomial : D05.Specs.PolynomialPolarization.HomogeneityExample.notPolynomial := by
  rintro ⟨p, hp⟩
  have hid : p * ((MvPolynomial.X (0 : Fin 2)) ^ 2 + MvPolynomial.X 1 ^ 2) =
      MvPolynomial.X 0 ^ 4 := by
    apply MvPolynomial.funext
    intro v
    simp only [map_mul, map_add, map_pow, MvPolynomial.eval_X, hp]
    exact multiply_denominator v
  have hc := congrArg (MvPolynomial.eval₂Hom Complex.ofRealHom ![Complex.I, 1]) hid
  norm_num [Complex.I_sq, pow_succ] at hc

end D05.M15.PolynomialPolarization.HomogeneityExample
