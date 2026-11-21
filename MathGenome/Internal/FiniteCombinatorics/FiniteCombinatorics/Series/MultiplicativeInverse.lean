import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.GeneratingSeries
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.MultiplicativeInverse
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Lean.Elab.Tactic.Omega

/-! The multiplicative inverse assertion of p204:W12, over any commutative
ring with identity. No domain, nontriviality, or field assumption is used. -/

noncomputable section
universe u

namespace FiniteCombinatorics.Series

theorem exists_inverse_iff_unit_constant {R : Type u} [CommRing R]
    (A : PowerSeries R) :
    (∃ C : PowerSeries R, A * C = 1 ∧ C * A = 1) ↔
      IsUnit (PowerSeries.constantCoeff A) := by
  constructor
  · rintro ⟨C, hAC, _⟩
    apply isUnit_iff_exists_inv.mpr
    exact ⟨PowerSeries.constantCoeff C, by
      simpa using congrArg PowerSeries.constantCoeff hAC⟩
  · rintro ⟨a₀, ha₀⟩
    exact ⟨PowerSeries.invOfUnit A a₀,
      PowerSeries.mul_invOfUnit A a₀ ha₀.symm,
      PowerSeries.invOfUnit_mul A a₀ ha₀.symm⟩

theorem invOfUnit_two_sided {R : Type u} [CommRing R]
    (A : PowerSeries R) (a₀ : Rˣ)
    (h : PowerSeries.constantCoeff A = (a₀ : R)) :
    A * PowerSeries.invOfUnit A a₀ = 1 ∧
      PowerSeries.invOfUnit A a₀ * A = 1 :=
  ⟨PowerSeries.mul_invOfUnit A a₀ h, PowerSeries.invOfUnit_mul A a₀ h⟩

theorem coeff_invOfUnit_zero {R : Type u} [CommRing R]
    (A : PowerSeries R) (a₀ : Rˣ)
    (_h : PowerSeries.constantCoeff A = (a₀ : R)) :
    PowerSeries.coeff 0 (PowerSeries.invOfUnit A a₀) = (↑a₀⁻¹ : R) := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    PowerSeries.constantCoeff_invOfUnit A a₀

theorem coeff_invOfUnit_recurrence {R : Type u} [CommRing R]
    (A : PowerSeries R) (a₀ : Rˣ)
    (_h : PowerSeries.constantCoeff A = (a₀ : R))
    (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n (PowerSeries.invOfUnit A a₀) =
      -(↑a₀⁻¹ : R) * ∑ i ∈ Finset.Icc 1 n,
        PowerSeries.coeff i A *
          PowerSeries.coeff (n - i) (PowerSeries.invOfUnit A a₀) := by
  classical
  rw [PowerSeries.coeff_invOfUnit, ite_eq_right (by omega),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hset : (Finset.range n.succ).filter (fun i => n - i < n) =
      Finset.Icc 1 n := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  simp only
  rw [← Finset.sum_filter, hset]

end FiniteCombinatorics.Series
