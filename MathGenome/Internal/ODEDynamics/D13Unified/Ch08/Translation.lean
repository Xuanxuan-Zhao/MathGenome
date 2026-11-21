import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.Translation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch08.Monodromy
import Mathlib.Tactic.Ring

noncomputable section

namespace D13Unified.Ch08.Translation
open D13Unified.Ch08.Monodromy

/-- Uniqueness and simultaneous periodicity of the canonical evolution
give the principal-matrix translation for all real times. -/
theorem one_period : Specs.D13Unified.Ch08.Translation.OnePeriod := by
  intro 𝕂 _ n A T hA _ hper t
  exact principal_period A hA T hper t

/-- Induction in both integer directions. The backward step uses the
proved invertibility of monodromy and the actual matrix inverse. -/
theorem integer_translation : Specs.D13Unified.Ch08.Translation.IntegerTranslation := by
  intro 𝕂 _ n A T hA _ hper k r
  change principalMatrix A ((k : ℝ) * T + r) =
    principalMatrix A r * monodromy A T ^ k
  have hM : IsUnit (monodromy A T).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp ((principal_properties 𝕂 n A hA).2 T)
  have hback (t : ℝ) : principalMatrix A (t - T) =
      principalMatrix A t * (monodromy A T)⁻¹ := by
    have h := congrArg (fun B => B * (monodromy A T)⁻¹)
      (principal_period A hA T hper (t - T))
    simpa only [sub_add_cancel, mul_assoc,
      Matrix.mul_nonsing_inv _ hM, mul_one] using h.symm
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have ht : (((k : ℤ) + 1 : ℤ) : ℝ) * T + r =
        (((k : ℤ) : ℝ) * T + r) + T := by
      push_cast
      ring
    rw [ht, principal_period A hA T hper, ih, Matrix.zpow_add_one hM, mul_assoc]
  | pred k ih =>
    simp only [Int.cast_neg] at ih
    have ht : ((-(k : ℤ) - 1 : ℤ) : ℝ) * T + r =
        (((-(k : ℤ)) : ℝ) * T + r) - T := by
      push_cast
      ring
    rw [ht, hback, ih, Matrix.zpow_sub_one hM, mul_assoc]

end D13Unified.Ch08.Translation
