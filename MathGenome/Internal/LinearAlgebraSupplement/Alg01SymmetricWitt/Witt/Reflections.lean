import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.Coordinates
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Reflections
import Mathlib.Tactic.Ring

namespace Alg01SymmetricWitt.Witt.Reflections

open Specs.Alg01SymmetricWitt.Witt.Reflections
open QuadraticMap (polar)

universe u v

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

private def reflectionLinear (q : QuadraticForm k V) (w : V) : V →ₗ[k] V :=
  LinearMap.id - (((q w)⁻¹ • q.polarBilin.flip w).smulRight w)

private theorem reflectionLinear_apply (q : QuadraticForm k V) (w x : V) :
    reflectionLinear q w x = x - (polar q x w / q w) • w := by
  simp [reflectionLinear, div_eq_inv_mul]

private theorem reflectionLinear_involutive (q : QuadraticForm k V) (w : V)
    (hw : q w ≠ 0) : Function.Involutive (reflectionLinear q w) := by
  intro x
  let c := polar q x w / q w
  have hc : c * q w = polar q x w := div_mul_cancel₀ _ hw
  have hp : polar q (reflectionLinear q w x) w = -(polar q x w) := by
    rw [reflectionLinear_apply, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_self]
    change polar q x w - c * (2 • q w) = _
    rw [two_nsmul, ← two_mul]
    calc
      polar q x w - c * (2 * q w) = polar q x w - 2 * (c * q w) := by ring
      _ = -(polar q x w) := by rw [hc]; ring
  rw [reflectionLinear_apply, hp, neg_div, neg_smul, sub_neg_eq_add,
    reflectionLinear_apply, sub_add_cancel]

private theorem reflectionLinear_preserves (q : QuadraticForm k V) (w : V)
    (hw : q w ≠ 0) (x : V) : q (reflectionLinear q w x) = q x := by
  let c := polar q x w / q w
  have hc : c * q w = polar q x w := div_mul_cancel₀ _ hw
  rw [reflectionLinear_apply]
  change q (x - c • w) = q x
  rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add q, q.map_smul,
    QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul]
  calc
    q x + (-c * -c) * q w + -c * polar q x w = q x + c * (c * q w - polar q x w) := by ring
    _ = q x := by rw [hc, sub_self, mul_zero, add_zero]

/-- The quadratic isometry that reflects in a vector of nonzero quadratic value. -/
def reflection (q : QuadraticForm k V) (w : V) (hw : q w ≠ 0) : q.IsometryEquiv q where
  toLinearEquiv := LinearEquiv.ofInvolutive (reflectionLinear q w)
    (reflectionLinear_involutive q w hw)
  map_app' := reflectionLinear_preserves q w hw

private theorem reflection_apply_polar (q : QuadraticForm k V) (w : V)
    (hw : q w ≠ 0) (x : V) : reflection q w hw x = x - (polar q x w / q w) • w :=
  reflectionLinear_apply q w x

theorem reflection_involutive (q : QuadraticForm k V) (w : V) (hw : q w ≠ 0) :
    Function.Involutive (reflection q w hw) :=
  reflectionLinear_involutive q w hw

theorem reflection_apply [Invertible (2 : k)] (q : QuadraticForm k V) (w : V)
    (hw : q w ≠ 0) (x : V) : reflection q w hw x = reflectionFormula q w x := by
  have htwo : (2 : k) ≠ 0 := Invertible.ne_zero _
  have hp : 2 * q.associated x w = polar q x w := by
    rw [Coordinates.associated_apply_div_two, mul_comm (2 : k), div_mul_cancel₀ _ htwo]
    rfl
  rw [reflectionFormula, hp, reflection_apply_polar]

/-- The displayed reflection formula defines an involutive linear isometry. -/
theorem reflectionIsometry : Specs.Alg01SymmetricWitt.Witt.Reflections.reflectionIsometry := by
  intro k V _ _ _ _ _ q _ w hw
  exact ⟨reflection q w hw, reflection_apply q w hw, reflection_involutive q w hw⟩

/-- Vectors of the same nonzero value are related by at most two reflections. -/
theorem moveByReflections : Specs.Alg01SymmetricWitt.Witt.Reflections.moveByReflections := by
  intro k V _ _ _ _ _ q _ x y a hx hy ha
  by_cases hxy : x = y
  · subst y
    exact ⟨QuadraticMap.IsometryEquiv.refl q, rfl, Or.inl rfl⟩
  by_cases hsub : q (x - y) = 0
  · have hp : polar q x y = q x + q y := by
      have h : 0 = q x + q y - polar q x y := by
        simpa only [← sub_eq_add_neg, q.map_neg, QuadraticMap.polar_neg_right, hsub] using
          QuadraticMap.map_add q x (-y)
      exact (sub_eq_zero.mp h.symm).symm
    have hsum : q (x + y) ≠ 0 := by
      have htwo : (2 : k) ≠ 0 := Invertible.ne_zero _
      have heq : q (x + y) = 2 * (2 * a) := by
        rw [QuadraticMap.map_add q x y, hp, hx, hy]
        ring
      rw [heq]
      exact mul_ne_zero htwo (mul_ne_zero htwo ha)
    have hy0 : q y ≠ 0 := hy.trans_ne ha
    let s := reflection q (x + y) hsum
    let t := reflection q y hy0
    have hs : s x = -y := by
      change reflection q (x + y) hsum x = -y
      have h : polar q x (x + y) = q (x + y) := by
        rw [QuadraticMap.polar_add_right, QuadraticMap.polar_self,
          QuadraticMap.map_add q x y, hx, hy]
        rw [two_nsmul]
      rw [reflection_apply_polar, h, div_self hsum, one_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
    have ht : t (-y) = y := by
      change reflection q y hy0 (-y) = y
      have h : polar q (-y) y / q y = -(2 : k) := by
        rw [QuadraticMap.polar_neg_left, QuadraticMap.polar_self, two_nsmul, ← two_mul,
          neg_div, mul_div_cancel_right₀ _ hy0]
      rw [reflection_apply_polar, h, neg_smul, sub_neg_eq_add, two_smul]
      abel
    exact ⟨s.trans t, show t (s x) = y by rw [hs, ht], Or.inr (Or.inr
      ⟨s, t, ⟨x + y, hsum, reflection_apply q _ hsum⟩,
        ⟨y, hy0, reflection_apply q _ hy0⟩, rfl⟩)⟩
  · have h : polar q x (x - y) = q (x - y) := by
      rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_self, sub_eq_add_neg x y,
        QuadraticMap.map_add q x (-y), q.map_neg, QuadraticMap.polar_neg_right, hx, hy]
      rw [two_nsmul, sub_eq_add_neg]
    have hs : reflection q (x - y) hsub x = y := by
      rw [reflection_apply_polar, h, div_self hsub, one_smul, sub_sub_cancel]
    exact ⟨reflection q _ hsub, hs, Or.inr (Or.inl ⟨x - y, hsub, reflection_apply q _ hsub⟩)⟩

end Alg01SymmetricWitt.Witt.Reflections
