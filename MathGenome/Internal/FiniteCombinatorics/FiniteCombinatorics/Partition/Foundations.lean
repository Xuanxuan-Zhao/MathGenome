import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.Foundations

noncomputable section

namespace FiniteCombinatorics

/-- The shared list presentation of an integer partition (W24). -/
abbrev Partition : ℕ → Type := Partition.Specs.PartitionValue

namespace Partition

/-- Finitely supported multiplicities of positive parts, with prescribed weight. -/
abbrev Multiplicities : ℕ → Type := Specs.MultiplicitiesValue

/-- Forget the order on the decreasing list. -/
def toMathlib {n : ℕ} (p : Partition n) : Nat.Partition n where
  parts := p.val
  parts_pos hi := p.property.2.1 _ hi
  parts_sum := by simpa using p.property.2.2

/-- Sort the multiset of parts into decreasing order. -/
def ofMathlib {n : ℕ} (p : Nat.Partition n) : Partition n :=
  ⟨p.parts.sort (· ≥ ·), Multiset.pairwise_sort _ _,
    by
      intro i hi
      exact p.parts_pos (by simpa using hi),
    by simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum⟩

/-- The list and Mathlib multiset presentations are inverse. -/
def mathlibEquiv (n : ℕ) : Partition n ≃ Nat.Partition n where
  toFun := toMathlib
  invFun := ofMathlib
  left_inv p := by
    apply Subtype.ext
    change ((p.val : Multiset ℕ).sort (· ≥ ·)) = p.val
    exact (Multiset.coe_eq_coe.mp (Multiset.sort_eq (p.val : Multiset ℕ) (· ≥ ·))).eq_of_pairwise'
      (Multiset.pairwise_sort _ _) p.property.1
  right_inv p := by
    apply Nat.Partition.ext
    exact Multiset.sort_eq _ _

private def positiveEmbedding : ℕ+ ↪ ℕ := ⟨PNat.val, PNat.coe_injective⟩

/-- Extend positive multiplicities by zero at the zero index. -/
def extendMultiplicities (m : ℕ+ →₀ ℕ) : ℕ →₀ ℕ :=
  m.embDomain positiveEmbedding

@[simp] theorem extendMultiplicities_pos (m : ℕ+ →₀ ℕ) (i : ℕ+) :
    extendMultiplicities m (i : ℕ) = m i :=
  Finsupp.embDomain_apply_self _ _ _

@[simp] theorem extendMultiplicities_zero (m : ℕ+ →₀ ℕ) :
    extendMultiplicities m 0 = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact i.property.ne' hi

/-- Count occurrences of each positive integer in a multiset partition. -/
def mathlibToMultiplicities {n : ℕ} (p : Nat.Partition n) : Multiplicities n := by
  let m : ℕ+ →₀ ℕ := Finsupp.comapDomain (PNat.val : ℕ+ → ℕ) p.parts.toFinsupp
    PNat.coe_injective.injOn
  refine ⟨m, ?_⟩
  have hs : (↑p.parts.toFinsupp.support : Set ℕ) ⊆ Set.range positiveEmbedding := by
    intro i hi
    have hp : i ∈ p.parts := by simpa using hi
    exact ⟨⟨i, p.parts_pos hp⟩, rfl⟩
  have he : extendMultiplicities m = p.parts.toFinsupp :=
    Finsupp.embDomain_comapDomain hs
  have hw : m.sum (fun i k => (i : ℕ) * k) =
      (extendMultiplicities m).sum (fun i k => i * k) := by
    simpa only [extendMultiplicities, positiveEmbedding, Function.Embedding.coeFn_mk] using
      (Finsupp.sum_embDomain (v := m) (f := positiveEmbedding)
        (g := fun i k => i * k)).symm
  calc
    m.sum (fun i k => (i : ℕ) * k) =
        (extendMultiplicities m).sum (fun i k => i * k) := hw
    _ = p.parts.sum := by
      rw [he]
      simpa only [Nat.nsmul_eq_mul, mul_comm, Multiset.toFinsupp_toMultiset] using
        (Finsupp.sum_toMultiset p.parts.toFinsupp).symm
    _ = n := p.parts_sum

@[simp] theorem mathlibToMultiplicities_apply {n : ℕ} (p : Nat.Partition n) (i : ℕ+) :
    (mathlibToMultiplicities p).val i = p.parts.count (i : ℕ) := rfl

/-- Repeat each positive part according to its multiplicity. -/
def multiplicitiesToMathlib {n : ℕ} (m : Multiplicities n) : Nat.Partition n where
  parts := (extendMultiplicities m.val).toMultiset
  parts_pos := by
    intro i hi
    have hn : extendMultiplicities m.val i ≠ 0 := by simpa using hi
    exact Nat.pos_of_ne_zero (fun h => hn (by simp [h]))
  parts_sum := by
    rw [Finsupp.sum_toMultiset]
    change (m.val.embDomain positiveEmbedding).sum (fun i k => k • i) = n
    rw [Finsupp.sum_embDomain]
    simpa [positiveEmbedding, Function.Embedding.coeFn_mk, mul_comm] using m.property

@[simp] theorem extend_mathlibToMultiplicities {n : ℕ} (p : Nat.Partition n) :
    extendMultiplicities (mathlibToMultiplicities p).val = p.parts.toFinsupp := by
  apply Finsupp.embDomain_comapDomain
  intro i hi
  have hp : i ∈ p.parts := by simpa using hi
  exact ⟨⟨i, p.parts_pos hp⟩, rfl⟩

/-- Counts and repetition give the multiset–multiplicity bijection. -/
def mathlibMultiplicityEquiv (n : ℕ) : Nat.Partition n ≃ Multiplicities n where
  toFun := mathlibToMultiplicities
  invFun := multiplicitiesToMathlib
  left_inv p := by
    apply Nat.Partition.ext
    apply Multiset.ext.mpr
    intro i
    change ((extendMultiplicities (mathlibToMultiplicities p).val).toMultiset).count i =
      p.parts.count i
    simp only [Finsupp.count_toMultiset, extend_mathlibToMultiplicities,
      Multiset.toFinsupp_apply]
  right_inv m := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change (multiplicitiesToMathlib m).parts.count (i : ℕ) = m.val i
    simp only [multiplicitiesToMathlib, Finsupp.count_toMultiset, extendMultiplicities_pos]

/-- The multiplicity of a part is its occurrence count in the decreasing list. -/
def multiplicityEquiv (n : ℕ) : Partition n ≃ Multiplicities n :=
  (mathlibEquiv n).trans (mathlibMultiplicityEquiv n)

@[simp] theorem multiplicityEquiv_apply {n : ℕ} (p : Partition n) (i : ℕ+) :
    (multiplicityEquiv n p).val i = p.val.count (i : ℕ) := by
  change (p.val : Multiset ℕ).count (i : ℕ) = p.val.count (i : ℕ)
  simp

instance partitionFintype (n : ℕ) : Fintype (Partition n) :=
  Fintype.ofEquiv (Nat.Partition n) (mathlibEquiv n).symm

instance multiplicitiesFintype (n : ℕ) : Fintype (Multiplicities n) :=
  Fintype.ofEquiv (Nat.Partition n) (mathlibMultiplicityEquiv n)

/-- Existence of the representation equivalence, including its underlying parts. -/
theorem multiset_representation : Specs.MultisetRepresentation := by
  intro n
  exact ⟨mathlibEquiv n, fun _ => rfl⟩

/-- Existence of the multiplicity equivalence, including the count formula. -/
theorem multiplicity_representation : Specs.MultiplicityRepresentation := by
  intro n
  exact ⟨multiplicityEquiv n, fun p i => multiplicityEquiv_apply p i⟩

/-- Both presentations of partitions of any fixed weight are finite. -/
theorem finite_representations : Specs.FiniteRepresentations := by
  intro n
  exact ⟨inferInstance, inferInstance⟩

/-- Zero has exactly the empty decreasing list and the zero multiplicity function. -/
theorem zero_partition : Specs.ZeroPartition := by
  refine ⟨⟨⟨[], by simp⟩, rfl⟩, ?_, ⟨⟨0, by simp⟩, rfl⟩, ?_⟩
  · intro p
    have h := Nat.Partition.partition_zero_parts (toMathlib p)
    simpa only [toMathlib, Multiset.coe_eq_zero] using h
  · intro m
    apply Finsupp.ext
    intro i
    have h := Nat.Partition.partition_zero_parts (multiplicitiesToMathlib m)
    have hc := congrArg (Multiset.count (i : ℕ)) h
    simpa only [multiplicitiesToMathlib, Finsupp.count_toMultiset,
      extendMultiplicities_pos, Multiset.count_zero, Finsupp.zero_apply] using hc

end Partition
end FiniteCombinatorics
