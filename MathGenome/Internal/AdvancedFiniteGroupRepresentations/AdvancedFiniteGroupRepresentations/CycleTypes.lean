import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.Partitions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CycleTypes

/-! FR-A01 (Theorem 1.1): conjugacy classes and their sizes.
The library cycle type omits fixed points; `cyclePartition` includes them.
-/

open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev cyclePartition := @Specs.AdvancedFiniteGroupRepresentations.cyclePartition
abbrev cycleMultiplicity := @Specs.AdvancedFiniteGroupRepresentations.cycleMultiplicity
abbrev centralizerFactor := @Specs.AdvancedFiniteGroupRepresentations.centralizerFactor
abbrev conjugacyCyclePartition := @Specs.AdvancedFiniteGroupRepresentations.conjugacyCyclePartition

theorem cyclePartition_parts {n : ℕ} (σ : SymmetricGroup n) :
    (cyclePartition σ).parts = σ.cycleType + Multiset.replicate (n - σ.support.card) 1 := by
  simp only [cyclePartition, Specs.AdvancedFiniteGroupRepresentations.cyclePartition,
    Equiv.Perm.parts_partition, Fintype.card_fin]

theorem isConj_iff_cyclePartition_eq {n : ℕ} (σ τ : SymmetricGroup n) :
    IsConj σ τ ↔ cyclePartition σ = cyclePartition τ := by
  rw [Equiv.Perm.partition_eq_of_isConj, Nat.Partition.ext_iff, Nat.Partition.ext_iff]
  rfl

theorem fixedPoint_multiplicity {n : ℕ} (σ : SymmetricGroup n) :
    cycleMultiplicity (cyclePartition σ) 1 = Fintype.card (Function.fixedPoints σ) := by
  have h : σ.cycleType.count 1 = 0 := Multiset.count_eq_zero.mpr (by
    intro hm
    have := Equiv.Perm.two_le_of_mem_cycleType hm
    omega)
  simp only [cycleMultiplicity, Specs.AdvancedFiniteGroupRepresentations.cycleMultiplicity,
    cyclePartition_parts, Multiset.count_add, h, zero_add, Multiset.count_replicate,
    ite_true]
  simpa only [Fintype.card_fin, Equiv.Perm.sum_cycleType] using
    (Equiv.Perm.card_fixedPoints σ).symm

/-- Separate the singleton cycles from all cycles of length at least two. -/
lemma partition_parts_split {n : ℕ} (ν : Partition n) :
    ν.parts = ν.parts.filter (2 ≤ ·) + Multiset.replicate (ν.parts.count 1) 1 := by
  have h : ν.parts.filter (fun j => ¬ 2 ≤ j) = ν.parts.filter (· = 1) := by
    apply Multiset.filter_congr
    intro j hj
    have hp := ν.parts_pos hj
    omega
  rw [← Multiset.filter_eq' ν.parts 1, ← h]
  exact (Multiset.filter_add_not _ _).symm

theorem cyclePartition_surjective (n : ℕ) : Function.Surjective (@cyclePartition n) := by
  intro ν
  let m := ν.parts.filter (2 ≤ ·)
  have hs : m.sum + ν.parts.count 1 = n := by
    have h := ν.parts_sum
    rw [partition_parts_split ν, Multiset.sum_add] at h
    simpa using h
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin n)).mpr
    (show m.sum ≤ Fintype.card (Fin n) ∧ ∀ a ∈ m, 2 ≤ a from
      ⟨by simp only [Fintype.card_fin]; omega,
        fun a ha => (Multiset.mem_filter.mp ha).2⟩)
  refine ⟨σ, Nat.Partition.ext ?_⟩
  rw [cyclePartition_parts, ← Equiv.Perm.sum_cycleType, hσ]
  rw [partition_parts_split ν]
  congr 2
  omega

theorem conjugacyCyclePartition_mk {n : ℕ} (σ : SymmetricGroup n) :
    conjugacyCyclePartition (ConjClasses.mk σ) = cyclePartition σ := rfl

theorem conjugacyCyclePartition_bijective (n : ℕ) :
    Function.Bijective (@conjugacyCyclePartition n) := by
  constructor
  · intro c d h
    obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective c
    obtain ⟨τ, rfl⟩ := ConjClasses.mk_surjective d
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr
      ((isConj_iff_cyclePartition_eq σ τ).mpr h)
  · intro ν
    obtain ⟨σ, hσ⟩ := cyclePartition_surjective n ν
    exact ⟨ConjClasses.mk σ, hσ⟩

lemma factorial_product_add_ones (m : Multiset ℕ) (k : ℕ) (hm : 1 ∉ m) :
    (∏ j ∈ (m + Multiset.replicate k 1).toFinset,
      ((m + Multiset.replicate k 1).count j).factorial) =
      k.factorial * ∏ j ∈ m.toFinset, (m.count j).factorial := by
  have hsub : (m + Multiset.replicate k 1).toFinset ⊆ insert 1 m.toFinset := by
    intro j hj
    rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hj) with h | h
    · exact Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr h)
    · rw [Multiset.eq_of_mem_replicate h]
      exact Finset.mem_insert_self _ _
  have hext : (∏ j ∈ (m + Multiset.replicate k 1).toFinset,
      ((m + Multiset.replicate k 1).count j).factorial) =
      ∏ j ∈ insert 1 m.toFinset, ((m + Multiset.replicate k 1).count j).factorial := by
    apply Finset.prod_subset hsub
    intro j _ hj
    rw [Multiset.count_eq_zero.mpr (by exact fun h => hj (Multiset.mem_toFinset.mpr h))]
    rfl
  rw [hext, Finset.prod_insert (by simpa using hm)]
  have hone : (m + Multiset.replicate k 1).count 1 = k := by simp [hm]
  rw [hone]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hj1 : j ≠ 1 := by
    intro h
    subst j
    exact hm (Multiset.mem_toFinset.mp hj)
  simp [Multiset.count_add, Multiset.count_replicate, Ne.symm hj1]

lemma centralizerFactor_cyclePartition {n : ℕ} (σ : SymmetricGroup n) :
    centralizerFactor (cyclePartition σ) =
      (n - σ.cycleType.sum).factorial * σ.cycleType.prod *
        ∏ j ∈ σ.cycleType.toFinset, (σ.cycleType.count j).factorial := by
  have hm : 1 ∉ σ.cycleType := by
    intro h
    have := Equiv.Perm.two_le_of_mem_cycleType h
    omega
  change (∏ j ∈ (cyclePartition σ).parts.toFinset,
    j ^ (cyclePartition σ).parts.count j * ((cyclePartition σ).parts.count j).factorial) = _
  rw [Finset.prod_mul_distrib, ← Finset.prod_multiset_count,
    cyclePartition_parts, ← Equiv.Perm.sum_cycleType,
    factorial_product_add_ones _ _ hm]
  simp only [Multiset.prod_add, Multiset.prod_replicate, one_pow, mul_one]
  ac_rfl

theorem centralizer_card {n : ℕ} (σ : SymmetricGroup n) :
    Nat.card (Subgroup.centralizer ({σ} : Set (SymmetricGroup n))) =
      centralizerFactor (cyclePartition σ) := by
  rw [centralizerFactor_cyclePartition]
  simpa only [Fintype.card_fin] using Equiv.Perm.nat_card_centralizer σ

theorem conjugacyClass_card {n : ℕ} (σ : SymmetricGroup n) :
    Nat.card {τ : SymmetricGroup n // IsConj σ τ} =
      n.factorial / centralizerFactor (cyclePartition σ) := by
  rw [centralizerFactor_cyclePartition]
  simpa only [Fintype.card_fin, Set.coe_ofPred] using Equiv.Perm.card_isConj_eq σ

theorem centralizer_card_of_type {n : ℕ} (ν : Partition n) (σ : SymmetricGroup n)
    (h : cyclePartition σ = ν) :
    Nat.card (Subgroup.centralizer ({σ} : Set (SymmetricGroup n))) = centralizerFactor ν := by
  rw [← h]
  exact centralizer_card σ

theorem conjugacyClass_card_of_type {n : ℕ} (ν : Partition n) (σ : SymmetricGroup n)
    (h : cyclePartition σ = ν) :
    Nat.card {τ : SymmetricGroup n // IsConj σ τ} = n.factorial / centralizerFactor ν := by
  rw [← h]
  exact conjugacyClass_card σ

theorem empty_centralizerFactor : centralizerFactor emptyPartition = 1 := by
  simp [centralizerFactor, Specs.AdvancedFiniteGroupRepresentations.centralizerFactor]

theorem zero_cyclePartition (σ : SymmetricGroup 0) : cyclePartition σ = emptyPartition :=
  zero_partition_unique _

theorem zero_cardinalities (σ : SymmetricGroup 0) :
    Nat.card (Subgroup.centralizer ({σ} : Set (SymmetricGroup 0))) = 1 ∧
    Nat.card {τ : SymmetricGroup 0 // IsConj σ τ} = 1 := by
  rw [centralizer_card, conjugacyClass_card, zero_cyclePartition, empty_centralizerFactor]
  norm_num

end AdvancedFiniteGroupRepresentations
