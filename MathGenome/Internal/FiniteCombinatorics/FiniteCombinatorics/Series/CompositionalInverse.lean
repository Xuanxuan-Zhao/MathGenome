import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.CompositionalInverse
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.Substitution

/-! The compositional inverse of a formal power series, paper.tex, p204:W12. -/

noncomputable section

universe u

namespace FiniteCombinatorics.Series

/-- Linear coefficients multiply under substitution by a zero-constant series. -/
theorem coeff_one_compose {R : Type u} [CommRing R] (B C : PowerSeries R)
    (hC : PowerSeries.constantCoeff C = 0) :
    PowerSeries.coeff 1 (compose B C) =
      PowerSeries.coeff 1 B * PowerSeries.coeff 1 C := by
  rw [coeff_compose B C hC 1]
  simp [Finset.sum_range_succ]

/-- The existence of a right compositional inverse forces the linear
coefficient to be a unit, also over rings with zero divisors. -/
theorem isUnit_coeff_one_of_compose_eq_X {R : Type u} [CommRing R]
    (B C : PowerSeries R) (hC : PowerSeries.constantCoeff C = 0)
    (hBC : compose B C = PowerSeries.X) : IsUnit (PowerSeries.coeff 1 B) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨PowerSeries.coeff 1 C, ?_⟩
  rw [← coeff_one_compose B C hC, hBC]
  simp

/-- Zero-constant series admit two-sided zero-constant compositional inverses
if and only if their linear coefficients are units. -/
theorem exists_compositional_inverse_iff {R : Type u} [CommRing R]
    (B : PowerSeries R) (hB : PowerSeries.constantCoeff B = 0) :
    (∃ C : PowerSeries R, PowerSeries.constantCoeff C = 0 ∧
      compose B C = PowerSeries.X ∧ compose C B = PowerSeries.X) ↔
      IsUnit (PowerSeries.coeff 1 B) := by
  constructor
  · rintro ⟨C, hC, hBC, _⟩
    exact isUnit_coeff_one_of_compose_eq_X B C hC hBC
  · intro hB1
    exact ⟨B.substInvOfIsUnit hB1,
      PowerSeries.constantCoeff_substInvOfIsUnit B hB1,
      PowerSeries.subst_substInvOfIsUnit_right B hB hB1,
      PowerSeries.subst_substInvOfIsUnit_left B hB hB1⟩

/-- Any two zero-constant right compositional inverses coincide. In particular,
a two-sided zero-constant compositional inverse is unique. -/
theorem compositional_inverse_unique {R : Type u} [CommRing R]
    (B C D : PowerSeries R) (hB : PowerSeries.constantCoeff B = 0)
    (hC : PowerSeries.constantCoeff C = 0) (hD : PowerSeries.constantCoeff D = 0)
    (hBC : compose B C = PowerSeries.X) (hBD : compose B D = PowerSeries.X) :
    C = D := by
  have hB1 := isUnit_coeff_one_of_compose_eq_X B C hC hBC
  exact (PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X B hB hB1
    (PowerSeries.HasSubst.of_constantCoeff_zero' hC) hBC).trans
    (PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X B hB hB1
      (PowerSeries.HasSubst.of_constantCoeff_zero' hD) hBD).symm

/-- The inverse's linear coefficient is the inverse of the original unit. -/
theorem coeff_one_compositional_inverse {R : Type u} [CommRing R]
    (B C : PowerSeries R) (hB : PowerSeries.constantCoeff B = 0)
    (hB1 : IsUnit (PowerSeries.coeff 1 B))
    (hC : PowerSeries.constantCoeff C = 0) (hBC : compose B C = PowerSeries.X) :
    PowerSeries.coeff 1 C = ↑(hB1.unit⁻¹) := by
  rw [PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X B hB hB1
    (PowerSeries.HasSubst.of_constantCoeff_zero' hC) hBC]
  exact PowerSeries.coeff_one_substInvOfIsUnit B hB1

end FiniteCombinatorics.Series
