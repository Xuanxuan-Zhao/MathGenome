import MathGenome.Internal.Specs.D07.Ch15.SquareCircle
import MathGenome.Internal.D07.Ch12.RelativeAlgebraicClosure
import MathGenome.Internal.D07.Ch15.QuadraticTowerIff
import MathGenome.Internal.D07.Appendix.PiTranscendental

/-! Squaring the circle is impossible with rational initial unit data.
Finite real quadratic towers preserve algebraicity. The geometric criterion
therefore places every produced coordinate in the relative algebraic closure
of Q in R. Field operations on these coordinates make the squared distance
between any two constructible points algebraic, contradicting the proved
transcendence of pi if this distance were the area of the unit circle.
-/

namespace D07.Ch15.SquareCircle

open D07.Ch15.StraightedgeCompass
open Specs.D07.Ch15.SquareCircle

/-- Rational initial coordinates generate an algebraic real field. -/
theorem coordinateField_le_algebraicClosure (P : InitialData)
    (hP : RationalInitialCoordinates P) :
    coordinateField P ≤ algebraicClosure ℚ ℝ := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro a (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
  · obtain ⟨x, y, rfl⟩ := hP p hp
    exact mem_algebraicClosure_iff.mpr (isAlgebraic_ratCast ℚ x)
  · obtain ⟨x, y, rfl⟩ := hP p hp
    exact mem_algebraicClosure_iff.mpr (isAlgebraic_ratCast ℚ y)

/-- Every finite tower, with degree-one and degree-two steps permitted,
stays inside the relative algebraic closure whenever its base does. -/
theorem quadraticTower_le_algebraicClosure {K M : IntermediateField ℚ ℝ}
    (hK : K ≤ algebraicClosure ℚ ℝ) (h : QuadraticTower K M) :
    M ≤ algebraicClosure ℚ ℝ := by
  induction h with
  | base => exact hK
  | @step M previous E hf hd ih =>
    let : FiniteDimensional M E := hf
    let : Algebra.IsAlgebraic ℚ M := (le_algebraicClosure_iff ℚ ℝ M).mp ih
    let : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.trans ℚ M E
    intro x hx
    have ha : IsAlgebraic ℚ (⟨x, hx⟩ : E) := Algebra.IsAlgebraic.isAlgebraic _
    exact mem_algebraicClosure_iff.mpr (ha.algHom (E.val.restrictScalars ℚ))

/-- Both coordinates of every geometric output are algebraic. -/
theorem constructible_coordinates_algebraic (P : InitialData)
    (hP : RationalInitialCoordinates P) (p : Point) (hp : IsConstructible P p) :
    IsAlgebraic ℚ p.1 ∧ IsAlgebraic ℚ p.2 := by
  obtain ⟨M, ht, hx, hy⟩ := (QuadraticTowerIff.point_criterion P p).mp hp
  have hM := quadraticTower_le_algebraicClosure (coordinateField_le_algebraicClosure P hP) ht
  exact ⟨mem_algebraicClosure_iff.mp (hM hx), mem_algebraicClosure_iff.mp (hM hy)⟩

theorem constructible_real_algebraic : ConstructibleRealAlgebraic := by
  intro P hP a ha
  exact (constructible_coordinates_algebraic P hP (a, 0) ha).1

theorem sqrt_pi_not_constructible : SqrtPiNotConstructible := by
  intro P hP hs
  exact D07.Appendix.PiTranscendental.sqrt_pi_transcendental
    (constructible_real_algebraic P hP _ hs)

theorem no_constructible_side : NoConstructibleSide := by
  intro P hP s hs he
  apply D07.Appendix.PiTranscendental.pi_transcendental
  rw [← he]
  exact (constructible_real_algebraic P hP s hs).pow 2

theorem no_square_circle : NoSquareCircle := by
  rintro P hP ⟨a, b, ha, hb, he⟩
  obtain ⟨ha₁, ha₂⟩ := constructible_coordinates_algebraic P hP a ha
  obtain ⟨hb₁, hb₂⟩ := constructible_coordinates_algebraic P hP b hb
  have hd : IsAlgebraic ℚ (squaredDistance a b) :=
    ((ha₁.sub hb₁).pow 2).add ((ha₂.sub hb₂).pow 2)
  exact D07.Appendix.PiTranscendental.pi_transcendental (he ▸ hd)

end D07.Ch15.SquareCircle
