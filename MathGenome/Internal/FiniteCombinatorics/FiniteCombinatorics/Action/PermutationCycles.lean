import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.PermutationCycles

/-! Complete permutation cycles, including singleton fixed-point cycles. -/
namespace FiniteCombinatorics.Permutation

open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u
variable {X : Type u} [Fintype X]

noncomputable def cyclicOrbit (σ : Equiv.Perm X) (x : X) : Finset X :=
  PermutationCyclesSpec.cyclicOrbit σ x
noncomputable def cycles (σ : Equiv.Perm X) : Finset (Finset X) :=
  PermutationCyclesSpec.cycles σ
def cycleLength (C : Finset X) : ℕ := C.card
noncomputable def countCyclesOfLength (σ : Equiv.Perm X) (k : ℕ) : ℕ :=
  PermutationCyclesSpec.countCyclesOfLength σ k
noncomputable def totalCycles (σ : Equiv.Perm X) : ℕ :=
  PermutationCyclesSpec.totalCycles σ
noncomputable def fixedPoints (σ : Equiv.Perm X) : Finset X :=
  PermutationCyclesSpec.fixedPoints σ

@[simp] theorem mem_cyclicOrbit (σ : Equiv.Perm X) (x y : X) :
    y ∈ cyclicOrbit σ x ↔ σ.SameCycle x y := by
  classical
  simp [cyclicOrbit, PermutationCyclesSpec.cyclicOrbit]

@[simp] theorem self_mem_cyclicOrbit (σ : Equiv.Perm X) (x : X) :
    x ∈ cyclicOrbit σ x := (mem_cyclicOrbit σ x x).2 (Equiv.Perm.SameCycle.refl σ x)

theorem mem_cyclicOrbit_iff_pow (σ : Equiv.Perm X) (x y : X) :
    y ∈ cyclicOrbit σ x ↔ ∃ n : ℕ, (σ ^ n) x = y := by
  rw [mem_cyclicOrbit]
  exact ⟨fun h => h.exists_nat_pow_eq, fun ⟨n, hn⟩ =>
    ⟨(n : ℤ), by simpa only [zpow_natCast] using hn⟩⟩

theorem cyclicOrbit_eq_iff (σ : Equiv.Perm X) (x y : X) :
    cyclicOrbit σ x = cyclicOrbit σ y ↔ σ.SameCycle x y := by
  constructor
  · intro h
    exact (mem_cyclicOrbit σ x y).1 (h ▸ self_mem_cyclicOrbit σ y)
  · intro h
    ext z
    simp only [mem_cyclicOrbit]
    exact ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

@[simp] theorem mem_cycles (σ : Equiv.Perm X) (C : Finset X) :
    C ∈ cycles σ ↔ ∃ x, cyclicOrbit σ x = C := by
  classical
  simp [cycles, PermutationCyclesSpec.cycles, cyclicOrbit]

theorem cyclicOrbit_mem_cycles (σ : Equiv.Perm X) (x : X) :
    cyclicOrbit σ x ∈ cycles σ := (mem_cycles σ _).2 ⟨x, rfl⟩

theorem eq_cyclicOrbit_of_mem (σ : Equiv.Perm X) {C : Finset X}
    (hC : C ∈ cycles σ) {x : X} (hx : x ∈ C) : C = cyclicOrbit σ x := by
  obtain ⟨y, rfl⟩ := (mem_cycles σ C).1 hC
  exact (cyclicOrbit_eq_iff σ y x).2 ((mem_cyclicOrbit σ y x).1 hx)

theorem cycles_partition (σ : Equiv.Perm X) (x : X) :
    ∃! C : Finset X, C ∈ cycles σ ∧ x ∈ C := by
  refine ⟨cyclicOrbit σ x, ⟨cyclicOrbit_mem_cycles σ x, self_mem_cyclicOrbit σ x⟩, ?_⟩
  intro C hC
  exact eq_cyclicOrbit_of_mem σ hC.1 hC.2

theorem cycles_pairwise_disjoint (σ : Equiv.Perm X) :
    (↑(cycles σ) : Set (Finset X)).PairwiseDisjoint id := by
  classical
  intro C hC D hD hne
  apply Finset.disjoint_left.2
  intro x hxC hxD
  exact hne ((eq_cyclicOrbit_of_mem σ hC hxC).trans
    (eq_cyclicOrbit_of_mem σ hD hxD).symm)

theorem cycles_cover (σ : Equiv.Perm X) :
    (cycles σ).biUnion id = (Finset.univ : Finset X) := by
  classical
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  exact ⟨cyclicOrbit σ x, cyclicOrbit_mem_cycles σ x, self_mem_cyclicOrbit σ x⟩

theorem cycleLength_bounds (σ : Equiv.Perm X) (C : Finset X) (hC : C ∈ cycles σ) :
    0 < cycleLength C ∧ cycleLength C ≤ Fintype.card X := by
  obtain ⟨x, rfl⟩ := (mem_cycles σ C).1 hC
  exact ⟨Finset.card_pos.mpr ⟨x, self_mem_cyclicOrbit σ x⟩, Finset.card_le_univ _⟩

theorem sum_cycleLength (σ : Equiv.Perm X) :
    ∑ C ∈ cycles σ, cycleLength C = Fintype.card X := by
  classical
  simpa only [id_eq, cycleLength, cycles_cover, Finset.card_univ] using
    (Finset.card_biUnion (cycles_pairwise_disjoint σ)).symm

theorem cyclicOrbit_eq_singleton_iff (σ : Equiv.Perm X) (x : X) :
    cyclicOrbit σ x = {x} ↔ σ x = x := by
  classical
  constructor
  · intro h
    have hx : σ x ∈ cyclicOrbit σ x :=
      (mem_cyclicOrbit_iff_pow σ x (σ x)).2 ⟨1, by simp⟩
    simpa [h] using hx
  · intro h
    ext y
    rw [mem_cyclicOrbit, Finset.mem_singleton]
    exact ⟨fun hy => (hy.eq_of_left h).symm,
      fun hy => by subst y; exact Equiv.Perm.SameCycle.refl σ x⟩

theorem singleton_mem_cycles_iff (σ : Equiv.Perm X) (x : X) :
    {x} ∈ cycles σ ↔ σ x = x := by
  classical
  constructor
  · intro h
    exact (cyclicOrbit_eq_singleton_iff σ x).1
      (eq_cyclicOrbit_of_mem σ h (Finset.mem_singleton_self x)).symm
  · intro h
    rw [← (cyclicOrbit_eq_singleton_iff σ x).2 h]
    exact cyclicOrbit_mem_cycles σ x

@[simp] theorem mem_fixedPoints (σ : Equiv.Perm X) (x : X) :
    x ∈ fixedPoints σ ↔ σ x = x := by
  classical
  simp [fixedPoints, PermutationCyclesSpec.fixedPoints]

/-- Singleton formation bijects the fixed points with the cycles of length one. -/
theorem countCyclesOfLength_one (σ : Equiv.Perm X) :
    countCyclesOfLength σ 1 = (fixedPoints σ).card := by
  classical
  have h : (cycles σ).filter (fun C => cycleLength C = 1) =
      (fixedPoints σ).image (fun x => {x}) := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hC, hlen⟩
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hlen
      exact ⟨x, (mem_fixedPoints σ x).2 ((singleton_mem_cycles_iff σ x).1 hC), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(singleton_mem_cycles_iff σ x).2 ((mem_fixedPoints σ x).1 hx),
        by simp [cycleLength]⟩
  change ((cycles σ).filter (fun C => cycleLength C = 1)).card = _
  rw [h, Finset.card_image_of_injective _ Finset.singleton_injective]

theorem countCyclesOfLength_zero (σ : Equiv.Perm X) :
    countCyclesOfLength σ 0 = 0 := by
  classical
  change ((cycles σ).filter (fun C => cycleLength C = 0)).card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro C hC hlen
  exact (Nat.ne_of_gt (cycleLength_bounds σ C hC).1) hlen

theorem countCyclesOfLength_eq_zero_of_gt (σ : Equiv.Perm X) (k : ℕ)
    (hk : Fintype.card X < k) : countCyclesOfLength σ k = 0 := by
  classical
  change ((cycles σ).filter (fun C => cycleLength C = k)).card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro C hC hlen
  exact (Nat.not_le_of_gt hk) (hlen ▸ (cycleLength_bounds σ C hC).2)

theorem totalCycles_eq_card (σ : Equiv.Perm X) : totalCycles σ = (cycles σ).card := by
  classical
  change (∑ k ∈ Finset.Icc 1 (Fintype.card X),
    ((cycles σ).filter (fun C => cycleLength C = k)).card) = (cycles σ).card
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro C hC
  exact Finset.mem_Icc.mpr (cycleLength_bounds σ C hC)

theorem sum_length_mul_count (σ : Equiv.Perm X) :
    ∑ k ∈ Finset.Icc 1 (Fintype.card X), k * countCyclesOfLength σ k =
      Fintype.card X := by
  classical
  calc
    _ = ∑ k ∈ Finset.Icc 1 (Fintype.card X),
        ∑ C ∈ (cycles σ).filter (fun C => cycleLength C = k), cycleLength C := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_const_nat (fun C hC => (Finset.mem_filter.mp hC).2)]
      exact Nat.mul_comm _ _
    _ = ∑ C ∈ cycles σ, cycleLength C := by
      apply Finset.sum_fiberwise_of_maps_to
      intro C hC
      exact Finset.mem_Icc.mpr (cycleLength_bounds σ C hC)
    _ = _ := sum_cycleLength σ

@[simp] theorem cycles_empty [IsEmpty X] (σ : Equiv.Perm X) : cycles σ = ∅ := by
  classical
  simp [cycles, PermutationCyclesSpec.cycles]

@[simp] theorem countCyclesOfLength_empty [IsEmpty X] (σ : Equiv.Perm X) (k : ℕ) :
    countCyclesOfLength σ k = 0 := by
  classical
  change ((cycles σ).filter (fun C => cycleLength C = k)).card = 0
  simp

@[simp] theorem totalCycles_empty [IsEmpty X] (σ : Equiv.Perm X) : totalCycles σ = 0 := by
  rw [totalCycles_eq_card, cycles_empty, Finset.card_empty]

end FiniteCombinatorics.Permutation
