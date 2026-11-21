import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.Exhaustion
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.DivisorLattice
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteGaloisStages.UnionConverse

/-!
# Exhaustion of the specified algebraic closure (FT-E03)

Counting identifies any finite intermediate field with the root field of its
own degree. Algebraicity puts every ambient element in a finite simple
extension. Divisibility of indices then puts it in a factorial stage, whose
directed union is the entire chosen closure.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]

/-- A finite intermediate field is the root field indexed by its positive degree. -/
theorem finite_intermediateField_eq_rootField (F : IntermediateField k Ω)
    [FiniteDimensional k F] :
    0 < Module.finrank k F ∧ F = finiteRootField k Ω (Module.finrank k F) := by
  refine ⟨Module.finrank_pos, ?_⟩
  apply IntermediateField.toSubfield_injective
  apply finiteRootField_unique k Ω _ Module.finrank_pos F.toSubfield
  change Nat.card F = Fintype.card k ^ Module.finrank k F
  rw [Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card]

/-- The positive root fields are exactly the finite-degree intermediate fields. -/
theorem finite_intermediateField_iff (F : IntermediateField k Ω) :
    FiniteDimensional k F ↔ ∃ n : ℕ, 0 < n ∧ F = finiteRootField k Ω n := by
  constructor
  · intro h
    let := h
    exact ⟨Module.finrank k F, finite_intermediateField_eq_rootField k Ω F⟩
  · rintro ⟨n, hn, rfl⟩
    exact (finiteRootField_finite_galois k Ω n hn).1

/-- Over the finite base this also classifies fields finite as sets. -/
theorem finite_intermediateField_finite_iff (F : IntermediateField k Ω) :
    Finite F ↔ ∃ n : ℕ, 0 < n ∧ F = finiteRootField k Ω n := by
  constructor
  · intro h
    let := h
    exact (finite_intermediateField_iff k Ω F).mp inferInstance
  · rintro ⟨n, hn, rfl⟩
    exact (Nat.card_pos_iff.mp (by
      rw [finiteRootField_card k Ω n hn]
      exact pow_pos Fintype.card_pos n)).2

/-- Every element of the specified closure lies in a positive root field. -/
theorem mem_some_finiteRootField (x : Ω) :
    ∃ n : ℕ, 0 < n ∧ x ∈ finiteRootField k Ω n := by
  let F := IntermediateField.adjoin k ({x} : Set Ω)
  let : FiniteDimensional k F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  obtain ⟨hd, heq⟩ := finite_intermediateField_eq_rootField k Ω F
  refine ⟨Module.finrank k F, hd, ?_⟩
  rw [← heq]
  exact IntermediateField.mem_adjoin_simple_self k x

/-- This is a set union in the ambient closure, not only a lattice supremum. -/
theorem finiteRootField_iUnion :
    (⋃ n : ℕ, ⋃ (_ : 0 < n), (finiteRootField k Ω n : Set Ω)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn, hx⟩ := mem_some_finiteRootField k Ω x
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn, hx⟩⟩

/-- Factorials with positive indices are cofinal for divisibility. -/
theorem factorial_indices_cofinal (n : ℕ) (hn : 0 < n) :
    ∃ j : ℕ, 0 < j ∧ n ∣ j.factorial :=
  ⟨n, hn, Nat.dvd_factorial hn le_rfl⟩

/-- The positive factorial stages form a directed family of literal subfields. -/
theorem factorialRootFields_directed :
    Directed (· ≤ ·)
      (fun j : {j : ℕ // 0 < j} => finiteRootField k Ω j.val.factorial) := by
  intro i j
  refine ⟨⟨max i.val j.val, lt_of_lt_of_le i.property (le_max_left _ _)⟩, ?_, ?_⟩
  · exact finiteRootField_le_of_dvd k Ω (Nat.factorial_dvd_factorial (le_max_left _ _))
  · exact finiteRootField_le_of_dvd k Ω (Nat.factorial_dvd_factorial (le_max_right _ _))

/-- Each ambient element already lies in a positive factorial stage. -/
theorem mem_some_factorialRootField (x : Ω) :
    ∃ j : ℕ, 0 < j ∧ x ∈ finiteRootField k Ω j.factorial := by
  obtain ⟨n, hn, hx⟩ := mem_some_finiteRootField k Ω x
  obtain ⟨j, hj, hnj⟩ := factorial_indices_cofinal n hn
  exact ⟨j, hj, finiteRootField_le_of_dvd k Ω hnj hx⟩

theorem finiteRootField_factorial_iUnion :
    (⋃ j : ℕ, ⋃ (_ : 0 < j), (finiteRootField k Ω j.factorial : Set Ω)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j, hj, hx⟩ := mem_some_factorialRootField k Ω x
  exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hx⟩⟩

/-- The directed union of the factorial finite Galois stages is Galois. -/
theorem algebraicClosure_isGalois : IsGalois k Ω := by
  let E := fun j : {j : ℕ // 0 < j} => finiteRootField k Ω j.val.factorial
  let : Nonempty {j : ℕ // 0 < j} := ⟨⟨1, Nat.zero_lt_one⟩⟩
  apply isGalois_of_directed_union E (factorialRootFields_directed k Ω)
  · intro j
    exact (finiteRootField_finite_galois k Ω j.val.factorial (Nat.factorial_pos _)).1
  · intro j
    exact (finiteRootField_finite_galois k Ω j.val.factorial (Nat.factorial_pos _)).2
  · intro x
    obtain ⟨j, hj, hx⟩ := mem_some_factorialRootField k Ω x
    exact ⟨⟨j, hj⟩, hx⟩

/-- Its finite Galois intermediate fields are exactly the same positive root fields. -/
theorem finite_galois_intermediateField_iff (F : IntermediateField k Ω) :
    (FiniteDimensional k F ∧ IsGalois k F) ↔
      ∃ n : ℕ, 0 < n ∧ F = finiteRootField k Ω n := by
  constructor
  · intro h
    exact (finite_intermediateField_iff k Ω F).mp h.1
  · rintro ⟨n, hn, rfl⟩
    exact finiteRootField_finite_galois k Ω n hn

end AdvancedFieldTheory
