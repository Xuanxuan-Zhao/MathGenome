import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.Pentagonal
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.Tactic.Linarith

/-! Euler's pentagonal identity (p204:W29, identity assertion).
We reuse Mathlib's formal pentagonal theorem, checking its integer conventions
and giving coefficientwise, locally finite statements as well as the displayed
infinite-product equality. No analytic convergence assumption is made. -/

noncomputable section
open scoped PowerSeries.WithPiTopology

namespace FiniteCombinatorics.Partition

theorem pentagonal_exponent (j : ℤ) :
    (pentagonal j : ℤ) = j * (3 * j - 1) / 2 ∧
      2 * (pentagonal j : ℤ) = j * (3 * j - 1) :=
  ⟨natCast_pentagonal j, two_mul_natCast_pentagonal j⟩

theorem pentagonal_sign (j : ℤ) :
    (Int.negOnePow j : ℤ) = (-1 : ℤ) ^ j.natAbs :=
  Int.coe_negOnePow ℤ j

theorem pentagonal_locally_finite (n : ℕ) :
    Set.Finite {j : ℤ | pentagonal j ≤ n} :=
  (Set.finite_Iic n).preimage pentagonal_injective.injOn

/-- Every exponent at most n has its index between -n and n. -/
theorem index_bounds_of_pentagonal_le {j : ℤ} {n : ℕ} (h : pentagonal j ≤ n) :
    -(n : ℤ) ≤ j ∧ j ≤ (n : ℤ) := by
  have hp := two_mul_natCast_pentagonal j
  have hn : (pentagonal j : ℤ) ≤ (n : ℤ) := by exact_mod_cast h
  constructor
  · by_contra hj
    have hj' : j ≤ -1 := by omega
    nlinarith [mul_nonneg (by omega : 0 ≤ -j - 1) (by omega : 0 ≤ -j)]
  · by_contra hj
    have hj' : 1 ≤ j := by omega
    nlinarith [mul_nonneg (by omega : 0 ≤ j - 1) (by omega : 0 ≤ j)]

theorem coeff_pentagonal_series (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.pentagonalSeries ℤ) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        if pentagonal j = n then (-1 : ℤ) ^ j.natAbs else 0 := by
  classical
  by_cases hn : ∃ j, pentagonal j = n
  · obtain ⟨j, rfl⟩ := hn
    rw [PowerSeries.coeff_pentagonalSeries_pentagonal]
    symm
    calc
      _ = (if pentagonal j = pentagonal j then (-1 : ℤ) ^ j.natAbs else 0) := by
        apply Finset.sum_eq_single j
        · intro k hk hkj
          simp only [pentagonal_inj, hkj, ite_false]
        · intro hj
          exact (hj (Finset.mem_Icc.mpr (index_bounds_of_pentagonal_le le_rfl))).elim
      _ = _ := by simp
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ (by simpa using hn)]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    simp only [show pentagonal j ≠ n from fun h => hn ⟨j, h⟩, ite_false]

theorem pentagonal_series_eq_ogf :
    PowerSeries.pentagonalSeries ℤ = Series.ogf (fun n =>
      ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        if pentagonal j = n then (-1 : ℤ) ^ j.natAbs else 0) := by
  ext n
  simpa using coeff_pentagonal_series n

theorem euler_pentagonal_coefficients (n : ℕ) :
    ∀ᶠ s : Finset ℕ in Filter.atTop,
      PowerSeries.coeff n (∏ i ∈ s,
        (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℤ)) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        if pentagonal j = n then (-1 : ℤ) ^ j.natAbs else 0 := by
  simpa only [coeff_pentagonal_series] using
    PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq ℤ n

theorem hasProd_euler_pentagonal :
    HasProd (fun i : ℕ => (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℤ))
      (PowerSeries.pentagonalSeries ℤ) :=
  PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℤ

theorem hasSum_euler_pentagonal :
    HasSum (fun j : ℤ =>
      PowerSeries.C ((-1 : ℤ) ^ j.natAbs) *
        PowerSeries.X ^ (j * (3 * j - 1) / 2).toNat)
      (PowerSeries.pentagonalSeries ℤ) := by
  simpa only [pentagonal_def, Int.coe_negOnePow, map_pow,
    map_neg, map_one] using PowerSeries.WithPiTopology.hasSum_pentagonalSeries ℤ

theorem euler_pentagonal :
    (∏' i : ℕ, (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℤ)) =
      ∑' j : ℤ, PowerSeries.C ((-1 : ℤ) ^ j.natAbs) *
        PowerSeries.X ^ (j * (3 * j - 1) / 2).toNat :=
  hasProd_euler_pentagonal.tprod_eq.trans hasSum_euler_pentagonal.tsum_eq.symm

theorem pentagonal_constant_term :
    PowerSeries.coeff 0 (PowerSeries.pentagonalSeries ℤ) = 1 ∧
      PowerSeries.coeff 0
        (∏' i : ℕ, (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℤ)) = 1 := by
  have h : PowerSeries.coeff 0 (PowerSeries.pentagonalSeries ℤ) = 1 := by
    simpa [pentagonal_def] using
      PowerSeries.coeff_pentagonalSeries_pentagonal ℤ 0
  exact ⟨h, by rw [hasProd_euler_pentagonal.tprod_eq]; exact h⟩

end FiniteCombinatorics.Partition
