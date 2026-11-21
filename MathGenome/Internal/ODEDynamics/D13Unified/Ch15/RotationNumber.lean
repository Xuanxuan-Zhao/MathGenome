import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.RotationNumber
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.RotationLimit

/-! The complete rotation-number theorem for increasing circle lifts. -/
namespace D13Unified.Ch15.RotationNumber

open Filter
open scoped Topology
open CircleLift RotationLimit

theorem rotationNumber_tendsto (L : IncreasingLift) (x : ℝ) :
    Tendsto (fun n : ℕ => ((L : ℝ → ℝ)^[n] x - x) / (n : ℝ))
      atTop (𝓝 (rotationNumber L)) :=
  RotationLimit.rotationNumber_tendsto L x

theorem rotationNumber_shift (L : IncreasingLift) (k : ℤ) :
    rotationNumber (shiftLift L k) = rotationNumber L + (k : ℝ) :=
  RotationLimit.rotationNumber_shift L k

/-- The library criterion needs continuity, supplied by the actual real
homeomorphism in the shared lift. It does not require the fraction to be reduced. -/
theorem rotationNumber_eq_rat_iff (L : IncreasingLift) (p : ℤ) (q : ℕ) (hq : 0 < q) :
    rotationNumber L = (p : ℝ) / (q : ℝ) ↔
      ∃ x : ℝ, (L : ℝ → ℝ)^[q] x = x + (p : ℝ) := by
  have h := (toDegreeOneLift L).translationNumber_eq_rat_iff
    L.toHomeomorph.continuous (m := p) hq
  have hf : (toDegreeOneLift L : ℝ → ℝ) = (L : ℝ → ℝ) := rfl
  simp only [CircleDeg1Lift.coe_pow, hf] at h
  exact h

theorem rotationNumber_eq_int_div_int_iff (L : IncreasingLift) (p q : ℤ) (hq : 1 ≤ q) :
    rotationNumber L = (p : ℝ) / (q : ℝ) ↔
      ∃ x : ℝ, (L : ℝ → ℝ)^[q.toNat] x = x + (p : ℝ) := by
  have hqpos : 0 < q.toNat := by omega
  have hcast : (q.toNat : ℝ) = (q : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ q by omega)
  simpa only [hcast] using rotationNumber_eq_rat_iff L p q.toNat hqpos

/-- A return on the quotient is exactly an integer displacement of a real
representative. The return time need not be the least period. -/
theorem circle_return_iff (L : IncreasingLift) (q : ℕ) :
    (∃ y : Circle, (circleMap L)^[q] y = y) ↔
      ∃ p : ℤ, ∃ x : ℝ, (L : ℝ → ℝ)^[q] x = x + (p : ℝ) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := quotientMap_surjective y
    rw [circleMap_iterate] at hy
    obtain ⟨p, hp⟩ := (quotientMap_eq_iff _ _).mp hy
    exact ⟨p, x, hp⟩
  · rintro ⟨p, x, hx⟩
    refine ⟨quotientMap x, ?_⟩
    rw [circleMap_iterate]
    exact (quotientMap_eq_iff _ _).mpr ⟨p, hx⟩

theorem periodicPoint_iff_rational (L : IncreasingLift) :
    (∃ y : Circle, ∃ q : ℕ, 0 < q ∧ (circleMap L)^[q] y = y) ↔
      ∃ r : ℚ, rotationNumber L = (r : ℝ) := by
  constructor
  · rintro ⟨y, q, hq, hy⟩
    obtain ⟨p, x, hx⟩ := (circle_return_iff L q).mp ⟨y, hy⟩
    refine ⟨(p : ℚ) / (q : ℚ), ?_⟩
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    exact (rotationNumber_eq_rat_iff L p q hq).mpr ⟨x, hx⟩
  · rintro ⟨r, hr⟩
    have hfrac : rotationNumber L = (r.num : ℝ) / (r.den : ℝ) := by
      rw [hr, Rat.cast_def]
    obtain ⟨x, hx⟩ := (rotationNumber_eq_rat_iff L r.num r.den r.den_pos).mp hfrac
    obtain ⟨y, hy⟩ := (circle_return_iff L r.den).mpr ⟨r.num, x, hx⟩
    exact ⟨y, r.den, r.den_pos, hy⟩

end D13Unified.Ch15.RotationNumber
