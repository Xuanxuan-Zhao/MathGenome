import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.PowerSumsAlternants
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.YoungPermutationCharacter
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.WeightedFixedColorings

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev rowSize := @Specs.AdvancedFiniteGroupRepresentations.rowSize
abbrev RowDecomposition := @Specs.AdvancedFiniteGroupRepresentations.RowDecomposition
abbrev OrderedRowModule := @Specs.AdvancedFiniteGroupRepresentations.OrderedRowModule
abbrev orderedRowRepresentation := @Specs.AdvancedFiniteGroupRepresentations.orderedRowRepresentation
abbrev youngPermutationCharacter := @Specs.AdvancedFiniteGroupRepresentations.youngPermutationCharacter

/-- The trace on the actual permutation basis counts the fixed decompositions. -/
theorem youngPermutationCharacter_eq_card {n r} (μ : Fin r → ℕ) (σ : SymmetricGroup n) :
    youngPermutationCharacter μ σ =
      (Nat.card {q : @RowDecomposition n r μ // σ • q = q} : ℂ) := by
  classical
  rw [youngPermutationCharacter, Specs.AdvancedFiniteGroupRepresentations.youngPermutationCharacter,
    Representation.character, LinearMap.trace_eq_matrix_trace ℂ
      (MonoidAlgebra.basis (@RowDecomposition n r μ) ℂ)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply]
  simp only [Specs.AdvancedFiniteGroupRepresentations.orderedRowRepresentation,
    Representation.ofMulAction_single]
  change (∑ q : @RowDecomposition n r μ, (MonoidAlgebra.single (σ • q) 1).coeff q) = _
  simp only [MonoidAlgebra.coeff_single]
  simp [Finsupp.single_apply, Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm]

/-- The complete orbit of a moved label is the support of its cycle factor. -/
theorem cyclicOrbit_eq_support {n} (σ : SymmetricGroup n) (a : Fin n)
    (ha : σ a ≠ a) :
    FiniteCombinatorics.Permutation.cyclicOrbit σ a = (σ.cycleOf a).support := by
  ext b
  exact (FiniteCombinatorics.Permutation.mem_cyclicOrbit σ a b).trans
    (Equiv.Perm.mem_support_cycleOf_iff' ha).symm

/-- Supports distinguish cycle factors of a fixed permutation. -/
theorem cycleFactor_support_injective {n} (σ : SymmetricGroup n) :
    Set.InjOn (fun c : SymmetricGroup n => c.support) σ.cycleFactorsFinset := by
  intro c hc d hd h
  obtain ⟨a, ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
  change c.support = d.support at h
  have hb : a ∈ d.support := by rw [← h]; exact ha
  exact (Equiv.Perm.cycle_is_cycleOf ha hc).trans
    (Equiv.Perm.cycle_is_cycleOf hb hd).symm

/-- Each nontrivial complete orbit is the support of exactly one cycle factor. -/
theorem completeCycles_nontrivial {n} (σ : SymmetricGroup n) (k : ℕ) (hk : 1 < k) :
    (FiniteCombinatorics.Permutation.cycles σ).filter (fun D => D.card = k) =
      (σ.cycleFactorsFinset.filter (fun c => c.support.card = k)).image
        (fun c => c.support) := by
  classical
  ext D
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hD, hcard⟩
    obtain ⟨a, rfl⟩ := (FiniteCombinatorics.Permutation.mem_cycles σ D).mp hD
    have ha : σ a ≠ a := by
      intro ha
      have he := (FiniteCombinatorics.Permutation.cyclicOrbit_eq_singleton_iff σ a).mpr ha
      rw [he, Finset.card_singleton] at hcard
      omega
    refine ⟨σ.cycleOf a, ⟨Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr ha), ?_⟩, ?_⟩
    · rwa [← cyclicOrbit_eq_support σ a ha]
    · exact (cyclicOrbit_eq_support σ a ha).symm
  · rintro ⟨c, ⟨hc, hcard⟩, rfl⟩
    obtain ⟨a, ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    have hca := Equiv.Perm.cycle_is_cycleOf ha hc
    have hmove : σ a ≠ a := by
      exact Equiv.Perm.mem_support.mp
        (Equiv.Perm.mem_cycleFactorsFinset_support_le hc ha)
    refine ⟨?_, hcard⟩
    rw [hca, ← cyclicOrbit_eq_support σ a hmove]
    exact FiniteCombinatorics.Permutation.cyclicOrbit_mem_cycles σ a

/-- Agreement between complete cycle counts (including singletons) and the
multiplicities in the canonical partition of the permutation. -/
theorem countCompleteCycles_eq_multiplicity {n} (σ : SymmetricGroup n) (k : ℕ)
    (hk : 0 < k) :
    FiniteCombinatorics.Permutation.countCyclesOfLength σ k =
      cycleMultiplicity (cyclePartition σ) k := by
  classical
  by_cases h1 : k = 1
  · subst k
    rw [fixedPoint_multiplicity]
    rw [FiniteCombinatorics.Permutation.countCyclesOfLength_one]
    exact (Fintype.card_of_finset' (p := Function.fixedPoints σ)
      (FiniteCombinatorics.Permutation.fixedPoints σ)
      (fun a => by simp [Function.fixedPoints, Function.IsFixedPt])).symm
  · have hk' : 1 < k := by omega
    change ((FiniteCombinatorics.Permutation.cycles σ).filter
      (fun D => D.card = k)).card = _
    rw [completeCycles_nontrivial σ k hk', Finset.card_image_iff.mpr
      ((cycleFactor_support_injective σ).mono (Finset.filter_subset _ _))]
    rw [cycleMultiplicity, Specs.AdvancedFiniteGroupRepresentations.cycleMultiplicity,
      cyclePartition_parts, Multiset.count_add, Multiset.count_replicate,
      ite_eq_right (Ne.symm h1), add_zero, Equiv.Perm.CycleType.count_def]
    simp only [Fintype.card_subtype, Finset.univ_eq_attach, Finset.card_filter]
    exact (Finset.sum_attach σ.cycleFactorsFinset
      (fun c : SymmetricGroup n => if c.support.card = k then (1 : ℕ) else 0)).symm

/-- Cycle assignment expressed in the literal commuting polynomial alphabet. -/
theorem fixedColorings_weight_sum {n r} (σ : SymmetricGroup n) :
    (∑ f : FiniteCombinatorics.Action.fixedColorings (SymmetricGroup n)
      (Fin n) (Fin r) σ, ∏ a : Fin n, (MvPolynomial.X (f.val a) : Alphabet r)) =
        partitionPowerSum r (cyclePartition σ) := by
  classical
  rw [FiniteCombinatorics.Action.sum_fixed_colorWeight]
  simp only [Fintype.card_fin]
  have hc (k) (hk : k ∈ Finset.Icc 1 n) :
      FiniteCombinatorics.Action.countCycles (SymmetricGroup n) (Fin n) σ k =
        cycleMultiplicity (cyclePartition σ) k := by
    change FiniteCombinatorics.Permutation.countCyclesOfLength σ k = _
    exact countCompleteCycles_eq_multiplicity σ k (Finset.mem_Icc.mp hk).1
  change (∏ k ∈ Finset.Icc 1 n, powerSum r k ^
    FiniteCombinatorics.Action.countCycles (SymmetricGroup n) (Fin n) σ k) = _
  have he : (∏ k ∈ Finset.Icc 1 n, powerSum r k ^
      FiniteCombinatorics.Action.countCycles (SymmetricGroup n) (Fin n) σ k) =
      ∏ k ∈ Finset.Icc 1 n, powerSum r k ^ cycleMultiplicity (cyclePartition σ) k :=
    Finset.prod_congr rfl (fun k hk => congrArg (fun m => powerSum r k ^ m) (hc k hk))
  rw [he]
  change _ = ∏ k ∈ (cyclePartition σ).parts.toFinset,
    powerSum r k ^ cycleMultiplicity (cyclePartition σ) k
  symm
  apply Finset.prod_subset
  · intro k hk
    have hm := Multiset.mem_toFinset.mp hk
    exact Finset.mem_Icc.mpr ⟨(cyclePartition σ).parts_pos hm,
      Nat.le_trans (Multiset.le_sum_of_mem hm) (le_of_eq (cyclePartition σ).parts_sum)⟩
  · intro k _ hk
    have hm : k ∉ (cyclePartition σ).parts := by simpa using hk
    simp [cycleMultiplicity, Specs.AdvancedFiniteGroupRepresentations.cycleMultiplicity,
      Multiset.count_eq_zero.mpr hm]

/-- Multiplying one variable per label records exactly the fiber sizes. -/
theorem prod_X_eq_rowSize_monomial {n r} (f : Fin n → Fin r) :
    (∏ a, (MvPolynomial.X (f a) : Alphabet r)) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (rowSize f)) 1 := by
  classical
  calc
    _ = ∏ i : Fin r, (MvPolynomial.X i : Alphabet r) ^ rowSize f i := by
      rw [← Fintype.prod_fiberwise' f (fun i => (MvPolynomial.X i : Alphabet r))]
      simp [rowSize, Specs.AdvancedFiniteGroupRepresentations.rowSize,
        Nat.card_eq_fintype_card]
    _ = _ := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      rfl

/-- Coefficient extraction imposes all row sizes, including the zero sizes. -/
theorem naturalCoefficient_prod_X {n r} (μ : Fin r → ℕ) (f : Fin n → Fin r) :
    naturalCoefficient μ (∏ a, (MvPolynomial.X (f a) : Alphabet r)) =
      if ∀ i, rowSize f i = μ i then 1 else 0 := by
  classical
  rw [prod_X_eq_rowSize_monomial]
  change (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (rowSize f))
    (1 : ℂ)).coeff (Finsupp.equivFunOnFinite.symm μ) = _
  rw [MvPolynomial.coeff_monomial]
  congr 1
  exact propext ⟨fun h i => congrFun (Finsupp.equivFunOnFinite.symm.injective h) i,
    fun h => congrArg Finsupp.equivFunOnFinite.symm (funext h)⟩

/-- The same fixed row assignment, viewed before or after imposing row sizes. -/
def fixedRowDecompositionEquiv {n r} (μ : Fin r → ℕ) (σ : SymmetricGroup n) :
    {q : @RowDecomposition n r μ // σ • q = q} ≃
      {f : FiniteCombinatorics.Action.fixedColorings (SymmetricGroup n)
        (Fin n) (Fin r) σ // ∀ i, rowSize f.val i = μ i} where
  toFun q := ⟨⟨q.val.val, congrArg Subtype.val q.property⟩, q.val.property⟩
  invFun f := ⟨⟨f.val.val, f.property⟩, Subtype.ext f.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- FR-C01 for an arbitrary ordered vector of nonnegative row sizes. In fact,
the equality also holds if the sizes do not sum to n, when both sides vanish. -/
theorem young_permutation_character_of_permutation {n r} (μ : Fin r → ℕ)
    (σ : SymmetricGroup n) :
    youngPermutationCharacter μ σ =
      naturalCoefficient μ (partitionPowerSum r (cyclePartition σ)) := by
  classical
  rw [youngPermutationCharacter_eq_card, Nat.card_congr (fixedRowDecompositionEquiv μ σ)]
  rw [← fixedColorings_weight_sum σ]
  change _ = (∑ f : FiniteCombinatorics.Action.fixedColorings (SymmetricGroup n)
    (Fin n) (Fin r) σ, ∏ a, (MvPolynomial.X (f.val a) : Alphabet r)).coeff
      (Finsupp.equivFunOnFinite.symm μ)
  rw [MvPolynomial.coeff_sum]
  change _ = ∑ f : FiniteCombinatorics.Action.fixedColorings (SymmetricGroup n)
    (Fin n) (Fin r) σ, naturalCoefficient μ (∏ a, (MvPolynomial.X (f.val a) : Alphabet r))
  simp_rw [naturalCoefficient_prod_X]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The character at any representative of the specified conjugacy class. -/
theorem young_permutation_character {n r} (μ : Fin r → ℕ) (_hμ : (∑ i, μ i) = n)
    (ν : Partition n) (σ : SymmetricGroup n) (hσ : cyclePartition σ = ν) :
    youngPermutationCharacter μ σ = naturalCoefficient μ (partitionPowerSum r ν) := by
  simpa only [hσ] using young_permutation_character_of_permutation μ σ

end AdvancedFiniteGroupRepresentations
