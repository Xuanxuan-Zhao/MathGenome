import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CycleTypes
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.PowerSumsAlternants

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations
abbrev Alphabet := Specs.AdvancedFiniteGroupRepresentations.Alphabet
abbrev powerSum := Specs.AdvancedFiniteGroupRepresentations.powerSum
abbrev partitionPowerSum := @Specs.AdvancedFiniteGroupRepresentations.partitionPowerSum
abbrev zFactor := @Specs.AdvancedFiniteGroupRepresentations.zFactor
abbrev staircase := Specs.AdvancedFiniteGroupRepresentations.staircase
abbrev alternant := @Specs.AdvancedFiniteGroupRepresentations.alternant
abbrev vandermonde := Specs.AdvancedFiniteGroupRepresentations.vandermonde
abbrev naturalCoefficient := @Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient
abbrev coefficient := @Specs.AdvancedFiniteGroupRepresentations.coefficient

theorem coefficient_of_negative {r} (b : Fin r → ℤ) (p : Alphabet r)
    (h : ∃ i, b i < 0) : coefficient b p = 0 := by
  rw [coefficient, Specs.AdvancedFiniteGroupRepresentations.coefficient, ite_eq_right]
  obtain ⟨i, hi⟩ := h
  exact fun hn => (not_le.mpr hi) (hn i)

theorem coefficient_of_nonnegative {r} (b : Fin r → ℤ) (p : Alphabet r)
    (h : ∀ i, 0 ≤ b i) :
    coefficient b p = naturalCoefficient (fun i => (b i).toNat) p := by
  simp [coefficient, Specs.AdvancedFiniteGroupRepresentations.coefficient, h]

theorem coefficient_natCast {r} (b : Fin r → ℕ) (p : Alphabet r) :
    coefficient (fun i => (b i : ℤ)) p = naturalCoefficient b p := by
  simp [coefficient, Specs.AdvancedFiniteGroupRepresentations.coefficient]

theorem powerSum_isHomogeneous (r j : ℕ) : (powerSum r j).IsHomogeneous j := by
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_X_pow i j)

theorem partitionPowerSum_isHomogeneous {n} (r : ℕ) (ν : Partition n) :
    (partitionPowerSum r ν).IsHomogeneous n := by
  have h := MvPolynomial.IsHomogeneous.prod ν.parts.toFinset
    (fun j => powerSum r j ^ cycleMultiplicity ν j)
    (fun j => j * ν.parts.count j)
    (fun j _ => (powerSum_isHomogeneous r j).pow (ν.parts.count j))
  have hs : (∑ j ∈ ν.parts.toFinset, j * ν.parts.count j) = n := by
    simpa [smul_eq_mul, mul_comm] using
      (Finset.sum_multiset_map_count ν.parts (fun j => j)).symm.trans (by simpa using ν.parts_sum)
  simpa only [partitionPowerSum, Specs.AdvancedFiniteGroupRepresentations.partitionPowerSum, hs] using h

theorem empty_partitionPowerSum (r : ℕ) : partitionPowerSum r emptyPartition = 1 := by
  simp [partitionPowerSum, Specs.AdvancedFiniteGroupRepresentations.partitionPowerSum,
    emptyPartition, Specs.AdvancedFiniteGroupRepresentations.emptyPartition]

theorem zero_alternant (b : Fin 0 → ℕ) : alternant b = 1 := by
  exact Matrix.det_isEmpty

theorem zero_vandermonde : vandermonde 0 = 1 := zero_alternant _

theorem zero_powerSum (j : ℕ) : powerSum 0 j = 0 := by
  simp [powerSum, Specs.AdvancedFiniteGroupRepresentations.powerSum]

/-- Reversing both indices reduces the decreasing-column alternant to the
library's increasing-column Vandermonde, without introducing a sign. -/
theorem vandermonde_product (r : ℕ) :
    vandermonde r = ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
      ((MvPolynomial.X i : Alphabet r) - MvPolynomial.X j) := by
  let x : Fin r → Alphabet r := MvPolynomial.X
  have hm : (Matrix.of fun i j : Fin r => x i ^ staircase r j) =
      (Matrix.vandermonde (fun i => x i.rev)).submatrix Fin.revPerm Fin.revPerm := by
    apply Matrix.ext
    intro i j
    change x i ^ (r - 1 - j.val) = x i.rev.rev ^ j.rev.val
    rw [Fin.rev_rev]
    congr 1
    simp only [Fin.val_rev]
    omega
  change (Matrix.of fun i j : Fin r => x i ^ staircase r j).det = _
  rw [hm, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde]
  calc
    (∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x j.rev - x i.rev)) =
        ∏ i : Fin r, ∏ j ∈ Finset.Iio i, (x j - x i) := by
      apply Fintype.prod_equiv Fin.revPerm
      intro i
      apply Finset.prod_equiv Fin.revPerm
      · intro j
        simp
      · intro j _
        rfl
    _ = ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x i - x j) := by
      simp only [← Finset.filter_gt_eq_Iio, ← Finset.filter_lt_eq_Ioi,
        Finset.prod_filter]
      rw [Finset.prod_comm]

end AdvancedFiniteGroupRepresentations
