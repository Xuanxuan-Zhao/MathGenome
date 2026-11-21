import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.RotationLimit
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.CircleLift

/-! Rotation limits, changes of lift, and the iterate/translation formula. -/
namespace D13Unified.Ch15.RotationLimit

open Filter
open scoped Topology
open CircleLift

noncomputable section

abbrev toDegreeOneLift : Specs.D13Unified.Ch15.RotationLimit.toDegreeOneLiftType :=
  Specs.D13Unified.Ch15.RotationLimit.toDegreeOneLift

abbrev rotationNumber : Specs.D13Unified.Ch15.RotationLimit.rotationNumberType :=
  Specs.D13Unified.Ch15.RotationLimit.rotationNumber

abbrev shiftLift : Specs.D13Unified.Ch15.RotationLimit.shiftLiftType :=
  Specs.D13Unified.Ch15.RotationLimit.shiftLift

abbrev iterateLift : Specs.D13Unified.Ch15.RotationLimit.iterateLiftType :=
  Specs.D13Unified.Ch15.RotationLimit.iterateLift

@[simp] theorem toDegreeOneLift_apply (L : IncreasingLift) (x : ℝ) :
    toDegreeOneLift L x = L x := rfl

theorem rotationNumber_tendsto (L : IncreasingLift) (x : ℝ) :
    Tendsto (fun n : ℕ => ((L : ℝ → ℝ)^[n] x - x) / (n : ℝ))
      atTop (𝓝 (rotationNumber L)) := by
  have hf : (toDegreeOneLift L : ℝ → ℝ) = (L : ℝ → ℝ) := rfl
  have h := (toDegreeOneLift L).tendsto_translationNumber x
  simp only [CircleDeg1Lift.coe_pow, hf] at h
  exact h

theorem exists_unique_rotationNumber (L : IncreasingLift) :
    ∃! ρ : ℝ, ∀ x : ℝ,
      Tendsto (fun n : ℕ => ((L : ℝ → ℝ)^[n] x - x) / (n : ℝ)) atTop (𝓝 ρ) := by
  refine ⟨rotationNumber L, rotationNumber_tendsto L, ?_⟩
  intro ρ hρ
  exact tendsto_nhds_unique (hρ 0) (rotationNumber_tendsto L 0)

@[simp] theorem shiftLift_apply (L : IncreasingLift) (k : ℤ) (x : ℝ) :
    shiftLift L k x = L x + (k : ℝ) := rfl

@[simp] theorem iterateLift_apply (L : IncreasingLift) (q : ℕ) (x : ℝ) :
    iterateLift L q x = (L : ℝ → ℝ)^[q] x := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change L (iterateLift L q x) = (L : ℝ → ℝ)^[q + 1] x
    rw [ih, Function.iterate_succ_apply']

/-- Integer translation commutes with every lift, so the displacement accumulates exactly. -/
theorem shiftLift_iterate (L : IncreasingLift) (k : ℤ) (n : ℕ) (x : ℝ) :
    (shiftLift L k : ℝ → ℝ)^[n] x = (L : ℝ → ℝ)^[n] x + (n : ℝ) * (k : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', shiftLift_apply, ih]
    have h := map_add_int L ((L : ℝ → ℝ)^[n] x) ((n : ℤ) * k)
    simp only [Int.cast_mul, Int.cast_natCast] at h
    rw [h, Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one]
    ring

private theorem toDegreeOneLift_shift (L : IncreasingLift) (k : ℤ) :
    toDegreeOneLift (shiftLift L k) =
      toDegreeOneLift L * (CircleDeg1Lift.translate (Multiplicative.ofAdd (k : ℝ)) :
        CircleDeg1Lift) := by
  apply CircleDeg1Lift.ext
  intro x
  change L x + (k : ℝ) = L ((k : ℝ) + x)
  rw [add_comm (k : ℝ) x, map_add_int]

theorem rotationNumber_shift (L : IncreasingLift) (k : ℤ) :
    rotationNumber (shiftLift L k) = rotationNumber L + (k : ℝ) := by
  have hc : Commute (toDegreeOneLift L)
      (CircleDeg1Lift.translate (Multiplicative.ofAdd (k : ℝ)) : CircleDeg1Lift) :=
    CircleDeg1Lift.commute_iff_commute.mpr ((toDegreeOneLift L).commute_int_add k)
  change (toDegreeOneLift (shiftLift L k)).translationNumber = _
  rw [toDegreeOneLift_shift, CircleDeg1Lift.translationNumber_mul_of_commute hc,
    CircleDeg1Lift.translationNumber_translate]
  rfl

private theorem toDegreeOneLift_iterate (L : IncreasingLift) (q : ℕ) :
    toDegreeOneLift (iterateLift L q) = toDegreeOneLift L ^ q := by
  apply CircleDeg1Lift.ext
  intro x
  rw [CircleDeg1Lift.coe_pow]
  exact iterateLift_apply L q x

theorem rotationNumber_iterate (L : IncreasingLift) (q : ℕ) :
    rotationNumber (iterateLift L q) = (q : ℝ) * rotationNumber L := by
  change (toDegreeOneLift (iterateLift L q)).translationNumber = _
  rw [toDegreeOneLift_iterate, CircleDeg1Lift.translationNumber_pow]
  rfl

/-- Exact identity for the lift `L^q - p`, with no assumption about periodic points. -/
theorem iterate_sub_int_identity (L : IncreasingLift) (q : ℕ) (p : ℤ) (n : ℕ) (x : ℝ) :
    (shiftLift (iterateLift L q) (-p) : ℝ → ℝ)^[n] x =
      (L : ℝ → ℝ)^[q * n] x - (n : ℝ) * (p : ℝ) := by
  rw [shiftLift_iterate]
  have hi : (iterateLift L q : ℝ → ℝ) = (L : ℝ → ℝ)^[q] :=
    funext (iterateLift_apply L q)
  rw [hi, ← Function.iterate_mul, Int.cast_neg]
  ring

theorem rotationNumber_iterate_sub_int (L : IncreasingLift) (q : ℕ) (p : ℤ) (_hq : 0 < q) :
    rotationNumber (shiftLift (iterateLift L q) (-p)) =
      (q : ℝ) * rotationNumber L - (p : ℝ) := by
  rw [rotationNumber_shift, rotationNumber_iterate, Int.cast_neg, sub_eq_add_neg]

end
end D13Unified.Ch15.RotationLimit
