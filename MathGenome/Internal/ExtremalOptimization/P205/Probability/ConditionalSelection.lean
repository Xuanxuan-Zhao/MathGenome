import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.ConditionalSelection
import MathGenome.Internal.ExtremalOptimization.P205.Probability.FiniteModels
import Mathlib.Tactic.FieldSimp

open scoped BigOperators Classical

namespace P205.Probability.ConditionalSelection

variable {Ω : Type*} [Fintype Ω]

noncomputable def conditionalMean (M : FiniteModel Ω) (Z : Ω → ℝ) (C : PositiveCell M) : ℝ :=
  mean M Z C

lemma cellMass_sum (M : FiniteModel Ω) (C : Finset Ω) :
    cellMass M C = ∑ ω ∈ C, M.weight ω := by
  simpa [cellMass] using M.eventMass_eq_sum (C : Set Ω)

lemma cellMass_nonneg (M : FiniteModel Ω) (C : Finset Ω) : 0 ≤ cellMass M C :=
  M.eventMass_nonneg _

/-- Zero mass forces every weight in the cell to vanish, even for signed objectives. -/
lemma cellMoment_zero_of_mass_zero (M : FiniteModel Ω) (Z : Ω → ℝ)
    (C : Finset Ω) (h : cellMass M C = 0) : cellMoment M Z C = 0 := by
  rw [cellMass_sum] at h
  have hw := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => M.weight_nonneg ω)).mp h
  exact Finset.sum_eq_zero (fun ω hω => by simp [hw ω hω])

lemma children_biUnion (P Q : Partition Ω) (hQP : Q ≤ P)
    (C : Finset Ω) (hC : C ∈ P.parts) : (children Q C).biUnion id = C := by
  classical
  ext ω
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨D, hD, hω⟩
    exact (Finset.mem_filter.mp hD).2 hω
  · intro hω
    obtain ⟨D, hD, hωD⟩ := Q.exists_mem (Finset.mem_univ ω)
    obtain ⟨E, hE, hDE⟩ := hQP hD
    have hEC : E = C := P.eq_of_mem_parts hE hC (hDE hωD) hω
    exact ⟨D, Finset.mem_filter.mpr ⟨hD, hEC ▸ hDE⟩, hωD⟩

lemma sum_children (P Q : Partition Ω) (hQP : Q ≤ P)
    (C : Finset Ω) (hC : C ∈ P.parts) (f : Ω → ℝ) :
    (∑ D ∈ children Q C, ∑ ω ∈ D, f ω) = ∑ ω ∈ C, f ω := by
  classical
  conv_rhs => rw [← children_biUnion P Q hQP C hC]
  apply (Finset.sum_biUnion _).symm
  intro D hD E hE hDE
  exact Q.disjoint (Finset.mem_filter.mp hD).1 (Finset.mem_filter.mp hE).1 hDE

lemma sum_positiveChildren (M : FiniteModel Ω) (Q : Partition Ω) (C : Finset Ω)
    (f : Finset Ω → ℝ) (hf : ∀ D, cellMass M D = 0 → f D = 0) :
    (∑ D ∈ positiveChildren M Q C, f D.val) = ∑ D ∈ children Q C, f D := by
  classical
  rw [positiveChildren, Finset.sum_subtype_eq_sum_filter]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hnpos : ¬ 0 < cellMass M D := by
    intro hp
    exact hn (Finset.mem_filter.mpr ⟨hD, hp⟩)
  exact hf D (le_antisymm (le_of_not_gt hnpos) (cellMass_nonneg M D))

theorem positive_child_masses (M : FiniteModel Ω) (P Q : Partition Ω) (hQP : Q ≤ P)
    (C : PositiveCell M) (hC : C.val ∈ P.parts) :
    (∑ D ∈ positiveChildren M Q C.val, cellMass M D.val) = cellMass M C.val := by
  rw [sum_positiveChildren M Q C.val _ (fun _ h => h)]
  simp_rw [cellMass_sum]
  exact sum_children P Q hQP C.val hC _

lemma positive_child_moments (M : FiniteModel Ω) (Z : Ω → ℝ)
    (P Q : Partition Ω) (hQP : Q ≤ P) (C : PositiveCell M) (hC : C.val ∈ P.parts) :
    (∑ D ∈ positiveChildren M Q C.val, cellMoment M Z D.val) = cellMoment M Z C.val := by
  rw [sum_positiveChildren M Q C.val _ (cellMoment_zero_of_mass_zero M Z)]
  exact sum_children P Q hQP C.val hC _

theorem parent_mean (M : FiniteModel Ω) (Z : Ω → ℝ)
    (P Q : Partition Ω) (hQP : Q ≤ P) (C : PositiveCell M) (hC : C.val ∈ P.parts) :
    mean M Z C = ∑ D ∈ positiveChildren M Q C.val,
      (cellMass M D.val / cellMass M C.val) * mean M Z D := by
  classical
  calc
    mean M Z C = (∑ D ∈ positiveChildren M Q C.val, cellMoment M Z D.val) /
        cellMass M C.val := by rw [positive_child_moments M Z P Q hQP C hC]; rfl
    _ = ∑ D ∈ positiveChildren M Q C.val, cellMoment M Z D.val / cellMass M C.val :=
      Finset.sum_div _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      dsimp [mean]
      field_simp [ne_of_gt C.property, ne_of_gt D.property]

theorem local_selection (M : FiniteModel Ω) (Z : Ω → ℝ)
    (P Q : Partition Ω) (hQP : Q ≤ P) (C : PositiveCell M) (hC : C.val ∈ P.parts) :
    ∃ D ∈ positiveChildren M Q C.val, mean M Z C ≤ mean M Z D := by
  classical
  have hmass := positive_child_masses M P Q hQP C hC
  have hne : (positiveChildren M Q C.val).Nonempty := by
    apply Finset.nonempty_of_sum_ne_zero (f := fun D : PositiveCell M => cellMass M D.val)
    rw [hmass]
    exact ne_of_gt C.property
  have havg := parent_mean M Z P Q hQP C hC
  have hsum : (∑ D ∈ positiveChildren M Q C.val,
      cellMass M D.val / cellMass M C.val) = 1 := by
    rw [← Finset.sum_div, hmass, div_self (ne_of_gt C.property)]
  obtain ⟨D, hD, hle⟩ := Finset.exists_le_of_sum_le hne (show
      (∑ D ∈ positiveChildren M Q C.val,
        (cellMass M D.val / cellMass M C.val) * mean M Z C) ≤
      ∑ D ∈ positiveChildren M Q C.val,
        (cellMass M D.val / cellMass M C.val) * mean M Z D by
    rw [← Finset.sum_mul, hsum, one_mul, ← havg])
  exact ⟨D, hD, (mul_le_mul_iff_right₀ (div_pos D.property C.property)).mp hle⟩

lemma cellMass_univ (M : FiniteModel Ω) : cellMass M Finset.univ = 1 := by
  rw [cellMass_sum]
  exact M.weight_sum

lemma mean_univ (M : FiniteModel Ω) (Z : Ω → ℝ)
    (C : PositiveCell M) (hC : C.val = Finset.univ) : mean M Z C = M.expectation Z := by
  simp only [mean, hC, cellMass_univ, div_one, cellMoment]
  rfl

/-- Local selection iterated through any finite refining prefix. -/
lemma exists_stage_path (M : FiniteModel Ω) (Z : Ω → ℝ) (n : ℕ)
    (P : ℕ → Partition Ω) (hstart : (P 0).parts = {Finset.univ})
    (hrefine : ∀ i, i < n → P (i + 1) ≤ P i) :
    ∃ C : ℕ → PositiveCell M, StagePath M Z P n C := by
  classical
  have hnext : ∀ i (C : PositiveCell M), ∃ D : PositiveCell M,
      (i < n → C.val ∈ (P i).parts →
        D.val ∈ (P (i + 1)).parts ∧ D.val ⊆ C.val ∧ mean M Z C ≤ mean M Z D) := by
    intro i C
    by_cases hi : i < n
    · by_cases hC : C.val ∈ (P i).parts
      · obtain ⟨D, hD, hmean⟩ := local_selection M Z (P i) (P (i + 1)) (hrefine i hi) C hC
        have hchild : D.val ∈ (P (i + 1)).parts ∧ D.val ⊆ C.val := by
          simpa only [positiveChildren, Finset.mem_subtype, children, Finset.mem_filter] using hD
        exact ⟨D, fun _ _ => ⟨hchild.1, hchild.2, hmean⟩⟩
      · exact ⟨C, fun _ h => False.elim (hC h)⟩
    · exact ⟨C, fun h _ => False.elim (hi h)⟩
  let step (i : ℕ) (C : PositiveCell M) : PositiveCell M := (hnext i C).choose
  have hstep (i : ℕ) (C : PositiveCell M) := (hnext i C).choose_spec
  let C0 : PositiveCell M := ⟨Finset.univ, by rw [cellMass_univ]; exact zero_lt_one⟩
  let C : ℕ → PositiveCell M := fun i => Nat.rec C0 (fun i D => step i D) i
  have hzero : C 0 = C0 := rfl
  have hsucc (i : ℕ) : C (i + 1) = step i (C i) := rfl
  have hmem : ∀ i, i ≤ n → (C i).val ∈ (P i).parts := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hzero, hstart]
      exact Finset.mem_singleton_self _
    | succ i ih =>
      intro hi
      have hin : i < n := Nat.lt_of_succ_le hi
      rw [hsucc]
      exact (hstep i (C i) hin (ih (Nat.le_of_lt hin))).1
  refine ⟨C, rfl, hmem, ?_⟩
  intro i hi
  rw [hsucc]
  exact (hstep i (C i) hi (hmem i (Nat.le_of_lt hi))).2

theorem staged_realization (M : FiniteModel Ω) (Z : Ω → ℝ) (n : ℕ)
    (P : ℕ → Partition Ω) (hstart : (P 0).parts = {Finset.univ})
    (hend : (P n).parts = Finset.univ.image (fun ω : Ω => ({ω} : Finset Ω)))
    (hrefine : ∀ i, i < n → P (i + 1) ≤ P i) :
    ∃ C : ℕ → PositiveCell M, StagePath M Z P n C ∧
      ∃ ω : Ω, (C n).val = {ω} ∧ 0 < M.weight ω ∧ mean M Z (C n) = Z ω ∧
        M.expectation Z ≤ Z ω := by
  classical
  obtain ⟨C, hC⟩ := exists_stage_path M Z n P hstart hrefine
  have hterminal := hC.2.1 n (le_refl n)
  rw [hend, Finset.mem_image] at hterminal
  obtain ⟨ω, _, hω⟩ := hterminal
  have hcell : (C n).val = {ω} := hω.symm
  have hpos : 0 < M.weight ω := by
    have h := (C n).property
    simpa only [hcell, cellMass_sum, Finset.sum_singleton] using h
  have hterminalMean : mean M Z (C n) = Z ω := by
    simp only [mean, hcell, cellMoment, cellMass_sum, Finset.sum_singleton]
    field_simp
  have hincreasing : ∀ i, i ≤ n → mean M Z (C 0) ≤ mean M Z (C i) := by
    intro i
    induction i with
    | zero => exact fun _ => le_refl _
    | succ i ih =>
      intro hi
      have hin : i < n := Nat.lt_of_succ_le hi
      exact (ih (Nat.le_of_lt hin)).trans (hC.2.2 i hin).2
  refine ⟨C, hC, ω, hcell, hpos, hterminalMean, ?_⟩
  rw [← hterminalMean, ← mean_univ M Z (C 0) hC.1]
  exact hincreasing n (le_refl n)

end P205.Probability.ConditionalSelection
