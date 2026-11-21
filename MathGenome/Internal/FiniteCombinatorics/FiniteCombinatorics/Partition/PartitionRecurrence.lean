import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.PartitionRecurrence
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Partition.EulerProduct
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Partition.Pentagonal

/-! The recurrence assertion of p204:W29. Coefficientwise stabilized finite
products give the inverse identity, and extraction of each coefficient pairs
positive and negative pentagonal indices. The final sum is algebraic and has
finite support. -/

noncomputable section
open scoped PowerSeries.WithPiTopology
open PowerSeries PowerSeries.WithPiTopology Filter

namespace FiniteCombinatorics.Partition

abbrev partitionNumber : ℤ → ℤ := RecurrenceSpecs.partitionNumberValue

@[simp] theorem partitionNumber_nat (n : ℕ) :
    partitionNumber n = (partitionCount n : ℤ) := by
  simp [partitionNumber, RecurrenceSpecs.partitionNumberValue]

@[simp] theorem partitionNumber_negative {m : ℤ} (h : m < 0) :
    partitionNumber m = 0 := by
  simp [partitionNumber, RecurrenceSpecs.partitionNumberValue, not_le.mpr h]

@[simp] theorem partitionNumber_zero : partitionNumber 0 = 1 := by
  rw [show (0 : ℤ) = (0 : ℕ) from rfl, partitionNumber_nat, partitionCount_eq_card]
  simp

private theorem finite_inverse (N : ℕ) :
    (∏ i ∈ Finset.range N, (1 - X ^ (i + 1) : PowerSeries ℤ)) *
      initialProduct ℤ N = 1 := by
  unfold initialProduct Specs.initialProductValue
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  exact (eulerFactor_inverse ℤ ⟨i + 1, Nat.succ_pos i⟩).1

/-- The two stabilized products are inverse formal power series. -/
theorem pentagonal_mul_partition_series :
    pentagonalSeries ℤ * mk (fun n => (partitionCount n : ℤ)) = 1 := by
  have hp := hasProd_euler_pentagonal.tendsto_prod_nat
  have hq : Tendsto (initialProduct ℤ) atTop
      (nhds (mk (fun n => (partitionCount n : ℤ)))) := by
    apply (tendsto_iff_coeff_tendsto ℤ _ _ _).mpr
    intro n
    apply tendsto_atTop_of_eventually_const
    intro N hN
    simpa using initialProduct_coeff ℤ n N hN
  have h := hp.mul hq
  have hc : (fun N => (∏ i ∈ Finset.range N,
      (1 - X ^ (i + 1) : PowerSeries ℤ)) * initialProduct ℤ N) = fun _ => 1 := by
    funext N
    exact finite_inverse N
  rw [hc] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

private theorem coeff_shift_partition (n d : ℕ) :
    coeff n (X ^ d * mk (fun i => (partitionCount i : ℤ))) =
      partitionNumber ((n : ℤ) - (d : ℤ)) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_mk, ← Int.natCast_sub h, partitionNumber_nat]
  · exact (partitionNumber_negative (by omega)).symm

/-- Coefficients of the product, with the integer zero extension built in. -/
private theorem hasSum_signed_partitions (n : ℕ) (hn : 0 < n) :
    HasSum (fun j : ℤ => (-1 : ℤ) ^ j.natAbs *
      partitionNumber ((n : ℤ) - (pentagonal j : ℤ))) 0 := by
  have h := (hasSum_euler_pentagonal.mul_right
    (mk (fun i => (partitionCount i : ℤ)))).map
    (coeff n) (continuous_coeff ℤ n)
  rw [pentagonal_mul_partition_series] at h
  simpa only [Function.comp_def, ← pentagonal_def,
    mul_assoc, coeff_C_mul, coeff_shift_partition, coeff_one, ite_eq_right hn.ne'] using h

private theorem pentagonal_neg_cast (k : ℤ) :
    (pentagonal (-k) : ℤ) = k * (3 * k + 1) / 2 := by
  rw [natCast_pentagonal]
  congr 1
  ring

private theorem recurrenceTerm_zero_of_lt (n : ℤ) (k : ℕ+) (h : n < (k : ℤ)) :
    RecurrenceSpecs.recurrenceTerm n k = 0 := by
  have h₁ := (index_bounds_of_pentagonal_le
    (j := (k : ℤ)) (n := pentagonal (k : ℤ)) le_rfl).2
  have h₂ := (index_bounds_of_pentagonal_le
    (j := -(k : ℤ)) (n := pentagonal (-(k : ℤ))) le_rfl).1
  unfold RecurrenceSpecs.recurrenceTerm
  rw [← natCast_pentagonal, ← pentagonal_neg_cast]
  change (-1 : ℤ) ^ ((k : ℕ) + 1) *
    (partitionNumber _ + partitionNumber _) = 0
  rw [partitionNumber_negative (by omega), partitionNumber_negative (by omega)]
  simp

/-- Only positive indices at most n can contribute. -/
theorem partition_recurrence_finite_support : RecurrenceSpecs.RecurrenceFiniteSupport := by
  intro n
  apply ((Set.finite_Iic n.toNat).preimage PNat.coe_injective.injOn).subset
  intro k hk
  change (k : ℕ) ≤ n.toNat
  by_contra h
  have hz := recurrenceTerm_zero_of_lt n k (by omega)
  exact hk hz

private theorem recurrenceTerm_eq_neg_pair (n : ℤ) (k : ℕ+) :
    RecurrenceSpecs.recurrenceTerm n k =
      -((-1 : ℤ) ^ (k : ℕ) * partitionNumber (n - (pentagonal (k : ℤ) : ℤ)) +
        (-1 : ℤ) ^ (k : ℕ) * partitionNumber (n - (pentagonal (-(k : ℤ)) : ℤ))) := by
  unfold RecurrenceSpecs.recurrenceTerm
  rw [natCast_pentagonal, pentagonal_neg_cast, pow_succ]
  ring

private theorem hasSum_recurrence (n : ℕ) (hn : 0 < n) :
    HasSum (RecurrenceSpecs.recurrenceTerm n) (partitionNumber n) := by
  let f : ℤ → ℤ := fun j => (-1 : ℤ) ^ j.natAbs *
    partitionNumber ((n : ℤ) - (pentagonal j : ℤ))
  have hf : HasSum f 0 := hasSum_signed_partitions n hn
  have hf0 : f 0 = partitionNumber n := by simp [f, pentagonal_def]
  have ht := (hasSum_nat_add_iff' 1).mpr hf.nat_add_neg
  have ht' : HasSum (fun k : ℕ => f ((k + 1 : ℕ) : ℤ) + f (-((k + 1 : ℕ) : ℤ)))
      (-partitionNumber n) := by
    simpa only [Finset.sum_range_one, Nat.cast_zero, neg_zero, hf0, zero_add,
      sub_add_eq_sub_sub, sub_self, zero_sub] using ht
  have hs : HasSum (fun k : ℕ =>
      RecurrenceSpecs.recurrenceTerm n ⟨k + 1, Nat.succ_pos k⟩)
      (partitionNumber n) := by
    convert ht'.neg using 1
    · funext k
      simpa only [f, PNat.mk_coe, Int.natAbs_natCast, Int.natAbs_neg] using
        recurrenceTerm_eq_neg_pair (n : ℤ) (⟨k + 1, Nat.succ_pos k⟩ : ℕ+)
    · simp
  exact Equiv.pnatEquivNat.symm.hasSum_iff.mp hs

/-- The finite-support sum is the recurrence in W29, for every positive integer. -/
theorem partition_recurrence : RecurrenceSpecs.PartitionRecurrence := by
  intro n hn
  have hs := hasSum_recurrence n.toNat (by omega)
  have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
  rw [he] at hs
  have hfin := partition_recurrence_finite_support n
  rw [finsum_eq_sum _ hfin]
  exact hs.unique (hasSum_sum_of_ne_finset_zero (fun k hk => by
    by_contra h
    exact hk (by simpa using h)))

end FiniteCombinatorics.Partition
