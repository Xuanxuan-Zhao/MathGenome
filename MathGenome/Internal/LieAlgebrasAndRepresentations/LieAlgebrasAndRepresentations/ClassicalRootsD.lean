import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsD
import Mathlib.Tactic.Abel
import Aesop
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Tauto

namespace LieAlgebrasAndRepresentations.ClassicalRootsD
open scoped Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsD

variable {n : ℕ}

/-- The defining equation in all four hyperbolic blocks. -/
theorem mem_algebra (X : Mat n) : X ∈ algebra n ↔
    (∀ i j, X (Sum.inr i) (Sum.inr j) = -X (Sum.inl j) (Sum.inl i)) ∧
    (∀ i j, X (Sum.inl i) (Sum.inr j) = -X (Sum.inl j) (Sum.inr i)) ∧
    (∀ i j, X (Sum.inr i) (Sum.inl j) = -X (Sum.inr j) (Sum.inl i)) := by
  simp only [algebra, LieAlgebra.Orthogonal.typeD,
    mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
    Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  change Xᵀ * LieAlgebra.Orthogonal.JD (Fin n) ℂ =
    LieAlgebra.Orthogonal.JD (Fin n) ℂ * (-X) ↔ _
  simp only [LieAlgebra.Orthogonal.JD]
  have hmul : ∀ (a b : Idx n), (Xᵀ * (Matrix.fromBlocks 0 1 1 0 : Mat n)) a b =
      X (Sum.swap b) a := by
    intro a b
    cases a <;> cases b <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hmul' : ∀ (a b : Idx n), ((Matrix.fromBlocks 0 1 1 0 : Mat n) * (-X)) a b =
      -X (Sum.swap a) b := by
    intro a b
    cases a <;> cases b <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  constructor
  · intro h
    have hh (a b : Idx n) := congrFun (congrFun h a) b
    simp only [hmul, hmul'] at hh
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa using hh (Sum.inr j) (Sum.inl i)
    · simpa using hh (Sum.inr j) (Sum.inr i)
    · simpa using hh (Sum.inl j) (Sum.inl i)
  · rintro ⟨hD, hB, hC⟩
    ext a b
    rw [hmul, hmul']
    cases a with
    | inl i => cases b with
      | inl j => exact hC j i
      | inr j => simpa using (congrArg Neg.neg (hD i j)).symm
    | inr i => cases b with
      | inl j => exact hD j i
      | inr j => exact hB j i

@[simp] theorem diagonal_mem (t : Params n) : diagonal n t ∈ algebra n := by
  rw [mem_algebra]
  simp only [diagonal, Matrix.diagonal_apply, Sum.inr.injEq, Sum.inl.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, ite_false, neg_zero, Pi.neg_apply, Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun i j => ?_, by simp, by simp⟩
  split_ifs with h <;> simp_all

@[simp] theorem aVector_mem (i j : Fin n) : aVector n i j ∈ algebra n := by
  rw [mem_algebra]
  simp [aVector, Matrix.single, eq_comm, and_comm]

@[simp] theorem bVector_mem (i j : Fin n) : bVector n i j ∈ algebra n := by
  rw [mem_algebra]
  simp [bVector, Matrix.single, eq_comm, and_comm, sub_eq_add_neg, add_comm]

@[simp] theorem cVector_mem (i j : Fin n) : cVector n i j ∈ algebra n := by
  rw [mem_algebra]
  simp [cVector, Matrix.single, eq_comm, and_comm, sub_eq_add_neg, add_comm]

/-- In particular, the two skew blocks have zero diagonal. -/
theorem skew_diagonal {X : Mat n} (hX : X ∈ algebra n) (i : Fin n) :
    X (Sum.inl i) (Sum.inr i) = 0 ∧ X (Sum.inr i) (Sum.inl i) = 0 := by
  obtain ⟨_, hB, hC⟩ := (mem_algebra X).mp hX
  constructor <;> [have hh := hB i i; have hh := hC i i] <;> linear_combination (1 / 2 : ℂ) * hh

@[simp] theorem rowWeight_apply (a : Idx n) (t : Params n) :
    rowWeight a t = Sum.elim t (-t) a := by cases a <;> rfl

/-- The diagonal commutator formula holds on every matrix entry. -/
theorem diagonal_bracket_entry (t : Params n) (X : Mat n) (a b : Idx n) :
    (diagonal n t * X - X * diagonal n t) a b =
      (rowWeight a t - rowWeight b t) * X a b := by
  simp [diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, sub_mul, mul_sub, mul_comm]

/-- A complete entrywise computation of every simultaneous weight space. -/
theorem mem_weightSpace (α : Dual n) (X : Mat n) :
    X ∈ weightSpace n α ↔ X ∈ algebra n ∧
      ∀ a b, X a b ≠ 0 → α = rowWeight a - rowWeight b := by
  constructor
  · rintro ⟨hX, he⟩
    refine ⟨hX, fun a b hab => ?_⟩
    apply LinearMap.ext
    intro t
    have h := congrFun (congrFun (he t) a) b
    rw [diagonal_bracket_entry] at h
    exact (mul_right_cancel₀ hab h).symm
  · rintro ⟨hX, he⟩
    refine ⟨hX, fun t => ?_⟩
    ext a b
    rw [diagonal_bracket_entry]
    by_cases h : X a b = 0
    · simp [h]
    · rw [he a b h]; rfl

private theorem sub_single_support (a b c d p q : Idx n)
    (h : ((Matrix.single a b (1 : ℂ) - Matrix.single c d 1) : Mat n) p q ≠ 0) :
    (p = a ∧ q = b) ∨ (p = c ∧ q = d) := by
  by_contra hn
  have h1 : ¬(a = p ∧ b = q) := by tauto
  have h2 : ¬(c = p ∧ d = q) := by tauto
  exact h (by simp [Matrix.single, h1, h2])

theorem aVector_weight (i j : Fin n) :
    aVector n i j ∈ weightSpace n (epsilon n i - epsilon n j) := by
  rw [mem_weightSpace]
  refine ⟨aVector_mem i j, ?_⟩
  intro a b h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := sub_single_support _ _ _ _ a b h
  · rfl
  · simp only [rowWeight, Sum.elim_inr]; abel

theorem bVector_weight (i j : Fin n) :
    bVector n i j ∈ weightSpace n (epsilon n i + epsilon n j) := by
  rw [mem_weightSpace]
  refine ⟨bVector_mem i j, ?_⟩
  intro a b h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := sub_single_support _ _ _ _ a b h
  all_goals simp only [rowWeight, Sum.elim_inl, Sum.elim_inr]; abel

theorem cVector_weight (i j : Fin n) :
    cVector n i j ∈ weightSpace n (-(epsilon n i + epsilon n j)) := by
  rw [mem_weightSpace]
  refine ⟨cVector_mem i j, ?_⟩
  intro a b h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := sub_single_support _ _ _ _ a b h
  all_goals simp only [rowWeight, Sum.elim_inl, Sum.elim_inr]; abel

@[simp] theorem epsilon_coordinate (i j : Fin n) :
    epsilon n i (coordinate n j) = if j = i then 1 else 0 := by
  simp [epsilon, coordinate, Pi.single_apply, eq_comm]

theorem epsilon_injective : Function.Injective (epsilon n) := by
  intro i j h
  by_contra hij
  have hh := LinearMap.congr_fun h (coordinate n i)
  simpa [hij] using hh

theorem epsilon_ne_neg (i j : Fin n) : epsilon n i ≠ -epsilon n j := by
  intro h
  have hh := LinearMap.congr_fun h (coordinate n i)
  by_cases hij : i = j <;> simp [hij] at hh
  · norm_num at hh

theorem rowWeight_injective : Function.Injective (@rowWeight n) := by
  intro a b h
  cases a with
  | inl i => cases b with
    | inl j => exact congrArg Sum.inl (epsilon_injective h)
    | inr j => exact False.elim (epsilon_ne_neg i j h)
  | inr i => cases b with
    | inl j => exact False.elim (epsilon_ne_neg j i h.symm)
    | inr j => exact congrArg Sum.inr (epsilon_injective (neg_injective h))

theorem diagonal_injective : Function.Injective (diagonal n) := by
  intro t u h
  funext i
  have hh := congrFun (congrFun h (Sum.inl i)) (Sum.inl i)
  simpa [diagonal] using hh

/-- The zero weight consists exactly of the displayed diagonal Cartan. -/
theorem zero_space (X : Mat n) : X ∈ weightSpace n 0 ↔ ∃ t, X = diagonal n t := by
  constructor
  · intro h
    obtain ⟨hX, hw⟩ := (mem_weightSpace 0 X).mp h
    have hoff (a b : Idx n) (hab : a ≠ b) : X a b = 0 := by
      by_contra hne
      have he : rowWeight a = rowWeight b := sub_eq_zero.mp (hw a b hne).symm
      exact hab (rowWeight_injective he)
    refine ⟨fun i => X (Sum.inl i) (Sum.inl i), ?_⟩
    ext a b
    cases a with
    | inl i => cases b with
      | inl j => by_cases hij : i = j <;> simp [diagonal, hij, hoff, *]
      | inr j => simp [diagonal, hoff]
    | inr i => cases b with
      | inl j => simp [diagonal, hoff]
      | inr j =>
        by_cases hij : i = j
        · subst j
          simpa [diagonal] using (mem_algebra X).mp hX |>.1 i i
        · simp [diagonal, hij, hoff, *]
  · rintro ⟨t, rfl⟩
    refine ⟨diagonal_mem t, fun u => ?_⟩
    ext a b
    rw [diagonal_bracket_entry]
    by_cases hab : a = b
    · subst b; simp
    · simp [diagonal, Matrix.diagonal_apply, hab]

theorem difference_ne_zero (i j : Fin n) (hij : i ≠ j) :
    epsilon n i - epsilon n j ≠ 0 := by
  exact fun h => hij (epsilon_injective (sub_eq_zero.mp h))

theorem sum_ne_zero (i j : Fin n) : epsilon n i + epsilon n j ≠ 0 := by
  exact fun h => epsilon_ne_neg i j (eq_neg_of_add_eq_zero_left h)

@[simp] theorem aVector_ne_zero (i j : Fin n) : aVector n i j ≠ 0 := by
  intro h
  have hh := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  simpa [aVector, Matrix.single] using hh

theorem bVector_ne_zero (i j : Fin n) (hij : i ≠ j) : bVector n i j ≠ 0 := by
  intro h
  have hh := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
  simpa [bVector, Matrix.single, hij] using hh

theorem cVector_ne_zero (i j : Fin n) (hij : i ≠ j) : cVector n i j ≠ 0 := by
  intro h
  have hh := congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
  simpa [cVector, Matrix.single, hij] using hh

/-- All nonzero weights, with no regularity assumption on diagonal parameters. -/
theorem roots_iff (α : Dual n) : α ∈ roots n ↔
    ∃ i j : Fin n, i ≠ j ∧
      (α = epsilon n i - epsilon n j ∨ α = epsilon n i + epsilon n j ∨
       α = -(epsilon n i + epsilon n j)) := by
  constructor
  · rintro ⟨ha, hs⟩
    obtain ⟨X, hX, hne⟩ := (Submodule.ne_bot_iff _).mp hs
    obtain ⟨a, b, hab⟩ : ∃ a b, X a b ≠ 0 := by
      by_contra! hh
      exact hne (by ext a b; exact hh a b)
    obtain ⟨horth, hw⟩ := (mem_weightSpace α X).mp hX
    have hα := hw a b hab
    cases a with
    | inl i => cases b with
      | inl j =>
        refine ⟨i, j, ?_, Or.inl hα⟩
        intro hij; subst j; exact ha (by simpa [rowWeight] using hα)
      | inr j =>
        refine ⟨i, j, ?_, Or.inr (Or.inl ?_)⟩
        · intro hij; subst j; exact hab ((skew_diagonal horth i).1)
        · simpa [rowWeight] using hα
    | inr i => cases b with
      | inl j =>
        refine ⟨i, j, ?_, Or.inr (Or.inr ?_)⟩
        · intro hij; subst j; exact hab ((skew_diagonal horth i).2)
        · exact hα.trans (by simp only [rowWeight, Sum.elim_inr, Sum.elim_inl]; abel)
      | inr j =>
        refine ⟨j, i, ?_, Or.inl ?_⟩
        · intro hij; subst j; exact ha (by simpa [rowWeight] using hα)
        · exact hα.trans (by simp only [rowWeight, Sum.elim_inr]; abel)
  · rintro ⟨i, j, hij, rfl | rfl | rfl⟩
    · exact ⟨difference_ne_zero i j hij,
        (Submodule.ne_bot_iff _).mpr ⟨_, aVector_weight i j, aVector_ne_zero i j⟩⟩
    · exact ⟨sum_ne_zero i j,
        (Submodule.ne_bot_iff _).mpr ⟨_, bVector_weight i j, bVector_ne_zero i j hij⟩⟩
    · exact ⟨neg_ne_zero.mpr (sum_ne_zero i j),
        (Submodule.ne_bot_iff _).mpr ⟨_, cVector_weight i j, cVector_ne_zero i j hij⟩⟩

/-- Reconstruction accounts for every entry allowed by the orthogonal equation. -/
theorem expansion (X : Mat n) (hX : X ∈ algebra n) :
    X = (∑ i, ∑ j, X (Sum.inl i) (Sum.inl j) • aVector n i j) +
      (1 / 2 : ℂ) • (∑ i, ∑ j, X (Sum.inl i) (Sum.inr j) • bVector n i j) +
      (1 / 2 : ℂ) • (∑ i, ∑ j, X (Sum.inr i) (Sum.inl j) • cVector n i j) := by
  obtain ⟨hD, hB, hC⟩ := (mem_algebra X).mp hX
  ext a b
  cases a <;> cases b <;>
    simp [aVector, bVector, cVector, Matrix.single, Matrix.sum_apply,
      Finset.sum_sub_distrib, mul_sub, ite_and]
  all_goals rename_i i j
  all_goals first | exact hD i j | linear_combination (1 / 2 : ℂ) * hB i j | linear_combination (1 / 2 : ℂ) * hC i j

/-- Explicit computation of *all* root spaces, also for weights absent from the table. -/
theorem weightSpace_eq_span (α : Dual n) :
    weightSpace n α = Submodule.span ℂ (generators n α) := by
  apply le_antisymm
  · intro X hX
    obtain ⟨horth, hw⟩ := (mem_weightSpace α X).mp hX
    rw [expansion X horth]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.sum_mem; intro i _
        apply Submodule.sum_mem; intro j _
        by_cases h : X (Sum.inl i) (Sum.inl j) = 0
        · simp [h]
        · apply Submodule.smul_mem
          apply Submodule.subset_span
          exact Or.inl (Or.inl ⟨i, j, hw _ _ h, rfl⟩)
      · apply Submodule.smul_mem
        apply Submodule.sum_mem; intro i _
        apply Submodule.sum_mem; intro j _
        by_cases h : X (Sum.inl i) (Sum.inr j) = 0
        · simp [h]
        · apply Submodule.smul_mem
          apply Submodule.subset_span
          exact Or.inl (Or.inr ⟨i, j, by simpa [rowWeight] using hw _ _ h, rfl⟩)
    · apply Submodule.smul_mem
      apply Submodule.sum_mem; intro i _
      apply Submodule.sum_mem; intro j _
      by_cases h : X (Sum.inr i) (Sum.inl j) = 0
      · simp [h]
      · apply Submodule.smul_mem
        apply Submodule.subset_span
        exact Or.inr ⟨i, j, by exact (hw _ _ h).trans (by simp only [rowWeight, Sum.elim_inr, Sum.elim_inl]; abel), rfl⟩
  · apply Submodule.span_le.mpr
    rintro X ((⟨i, j, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩) | ⟨i, j, rfl, rfl⟩)
    · exact aVector_weight i j
    · exact bVector_weight i j
    · exact cVector_weight i j

private theorem diff_eq_diff {i j k l : Fin n} (hij : i ≠ j)
    (h : epsilon n i - epsilon n j = epsilon n k - epsilon n l) : i = k ∧ j = l := by
  have hi := LinearMap.congr_fun h (coordinate n i)
  have hj := LinearMap.congr_fun h (coordinate n j)
  simp only [LinearMap.sub_apply, epsilon_coordinate, if_pos rfl, if_neg hij,
    if_neg (Ne.symm hij)] at hi hj
  split_ifs at hi hj <;> norm_num at hi <;> norm_num at hj <;> aesop

private theorem diff_ne_sum (i j k l : Fin n) (hij : i ≠ j) :
    epsilon n i - epsilon n j ≠ epsilon n k + epsilon n l := by
  intro h
  have hj := LinearMap.congr_fun h (coordinate n j)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, epsilon_coordinate, if_pos rfl,
    if_neg (Ne.symm hij)] at hj
  split_ifs at hj <;> norm_num at hj

private theorem diff_ne_neg_sum (i j k l : Fin n) (hij : i ≠ j) :
    epsilon n i - epsilon n j ≠ -(epsilon n k + epsilon n l) := by
  intro h
  have hi := LinearMap.congr_fun h (coordinate n i)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    epsilon_coordinate, if_pos rfl, if_neg hij] at hi
  split_ifs at hi <;> norm_num at hi

private theorem sum_ne_neg_sum (i j k l : Fin n) :
    epsilon n i + epsilon n j ≠ -(epsilon n k + epsilon n l) := by
  intro h
  have hi := LinearMap.congr_fun h (coordinate n i)
  simp only [LinearMap.add_apply, LinearMap.neg_apply, epsilon_coordinate, if_pos rfl] at hi
  split_ifs at hi <;> norm_num at hi

private theorem sum_eq_sum {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (h : epsilon n i + epsilon n j = epsilon n k + epsilon n l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hi := LinearMap.congr_fun h (coordinate n i)
  have hj := LinearMap.congr_fun h (coordinate n j)
  simp only [LinearMap.add_apply, epsilon_coordinate, if_pos rfl, if_neg hij,
    if_neg (Ne.symm hij)] at hi hj
  split_ifs at hi hj <;> norm_num at hi <;> norm_num at hj <;> aesop

/-- Each difference root space is the line through its displayed matrix unit pair. -/
theorem difference_space (i j : Fin n) (hij : i ≠ j) :
    weightSpace n (epsilon n i - epsilon n j) = Submodule.span ℂ {aVector n i j} := by
  rw [weightSpace_eq_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro X ((⟨k, l, he, rfl⟩ | ⟨k, l, he, rfl⟩) | ⟨k, l, he, rfl⟩)
    · obtain ⟨rfl, rfl⟩ := diff_eq_diff hij he
      exact Submodule.subset_span (Set.mem_singleton _)
    · exact False.elim (diff_ne_sum i j k l hij he)
    · exact False.elim (diff_ne_neg_sum i j k l hij he)
  · apply Submodule.span_mono
    intro X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    exact Or.inl (Or.inl ⟨i, j, rfl, rfl⟩)

@[simp] theorem bVector_self (i : Fin n) : bVector n i i = 0 := by exact sub_self _
@[simp] theorem cVector_self (i : Fin n) : cVector n i i = 0 := by exact sub_self _

theorem bVector_swap (i j : Fin n) : bVector n j i = -bVector n i j := by
  unfold bVector; abel

theorem cVector_swap (i j : Fin n) : cVector n j i = -cVector n i j := by
  unfold cVector; abel

/-- Each sum root space is the line through an upper-right skew matrix pair. -/
theorem sum_space (i j : Fin n) (hij : i ≠ j) :
    weightSpace n (epsilon n i + epsilon n j) = Submodule.span ℂ {bVector n i j} := by
  rw [weightSpace_eq_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro X ((⟨k, l, he, rfl⟩ | ⟨k, l, he, rfl⟩) | ⟨k, l, he, rfl⟩)
    · by_cases hkl : k = l
      · subst l; exact False.elim (sum_ne_zero i j (by simpa using he))
      · exact False.elim (diff_ne_sum k l i j hkl he.symm)
    · by_cases hkl : k = l
      · subst l; simp
      · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := sum_eq_sum hij hkl he
        · exact Submodule.subset_span (Set.mem_singleton _)
        · rw [bVector_swap i j]
          apply Submodule.neg_mem
          exact Submodule.subset_span (Set.mem_singleton _)
    · exact False.elim (sum_ne_neg_sum i j k l he)
  · apply Submodule.span_mono
    intro X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    exact Or.inl (Or.inr ⟨i, j, rfl, rfl⟩)

/-- Each negative sum root space is the corresponding lower-left skew line. -/
theorem neg_sum_space (i j : Fin n) (hij : i ≠ j) :
    weightSpace n (-(epsilon n i + epsilon n j)) = Submodule.span ℂ {cVector n i j} := by
  rw [weightSpace_eq_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro X ((⟨k, l, he, rfl⟩ | ⟨k, l, he, rfl⟩) | ⟨k, l, he, rfl⟩)
    · by_cases hkl : k = l
      · subst l; exact False.elim (neg_ne_zero.mpr (sum_ne_zero i j) (by simpa using he))
      · exact False.elim (diff_ne_neg_sum k l i j hkl he.symm)
    · exact False.elim (sum_ne_neg_sum k l i j he.symm)
    · by_cases hkl : k = l
      · subst l; simp
      · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := sum_eq_sum hij hkl (neg_injective he)
        · exact Submodule.subset_span (Set.mem_singleton _)
        · rw [cVector_swap i j]
          apply Submodule.neg_mem
          exact Submodule.subset_span (Set.mem_singleton _)
  · apply Submodule.span_mono
    intro X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    exact Or.inr ⟨i, j, rfl, rfl⟩

/-- The computed weight spaces span precisely the even orthogonal algebra. -/
theorem iSup_weightSpace : (⨆ α : Dual n, weightSpace n α) = (algebra n).toSubmodule := by
  apply le_antisymm
  · exact iSup_le fun α X hX => hX.1
  · intro X hX
    rw [expansion X hX]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.sum_mem; intro i _
        apply Submodule.sum_mem; intro j _
        apply Submodule.smul_mem
        exact le_iSup (weightSpace n) _ (aVector_weight i j)
      · apply Submodule.smul_mem
        apply Submodule.sum_mem; intro i _
        apply Submodule.sum_mem; intro j _
        apply Submodule.smul_mem
        exact le_iSup (weightSpace n) _ (bVector_weight i j)
    · apply Submodule.smul_mem
      apply Submodule.sum_mem; intro i _
      apply Submodule.sum_mem; intro j _
      apply Submodule.smul_mem
      exact le_iSup (weightSpace n) _ (cVector_weight i j)

/-- Distinct weights form a direct sum. The proof separates them entry by entry. -/
theorem weightSpace_independent : iSupIndep (weightSpace n) := by
  rw [iSupIndep_def]
  intro α
  rw [Submodule.disjoint_def]
  intro X hX hrest
  ext a b
  by_cases hab : X a b = 0
  · exact hab
  · let K : Submodule ℂ (Mat n) :=
      { carrier := {Y | Y a b = 0}
        zero_mem' := rfl
        add_mem' := by intro Y Z hY hZ; change Y a b + Z a b = 0; rw [hY, hZ, add_zero]
        smul_mem' := by intro c Y hY; change c * Y a b = 0; rw [hY, mul_zero] }
    have hK : (⨆ β : Dual n, ⨆ (_ : β ≠ α), weightSpace n β) ≤ K := by
      refine iSup_le fun β => iSup_le fun hβα => ?_
      intro Y hY
      change Y a b = 0
      by_contra hy
      exact hβα (((mem_weightSpace β Y).mp hY).2 a b hy |>.trans
        (((mem_weightSpace α X).mp hX).2 a b hab).symm)
    exact hK hrest

/-- The complete decomposition indexed by the Cartan and precisely the nonzero roots. -/
theorem root_decomposition : iSupIndep (summand n) ∧
    (⨆ a : Option (roots n), summand n a) = (algebra n).toSubmodule := by
  let f : Option (roots n) → Dual n := fun a => a.elim 0 Subtype.val
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | none => cases b with
      | none => rfl
      | some β => exact False.elim (β.property.1 h.symm)
    | some α => cases b with
      | none => exact False.elim (α.property.1 h)
      | some β => exact congrArg some (Subtype.ext h)
  have he : summand n = fun a => weightSpace n (f a) := by
    funext a; cases a <;> rfl
  refine ⟨he ▸ (weightSpace_independent (n := n)).comp hf, ?_⟩
  apply le_antisymm
  · refine iSup_le fun a X hX => ?_
    cases a <;> exact hX.1
  · rw [← iSup_weightSpace]
    refine iSup_le fun α => ?_
    by_cases hα : α = 0
    · subst α; exact le_iSup (summand n) none
    · by_cases hs : weightSpace n α = ⊥
      · rw [hs]; exact bot_le
      · exact le_iSup (summand n) (some ⟨α, hα, hs⟩)

/-- The stated diagonal space is self-normalizing as well as self-centralizing. -/
theorem normalizer_is_diagonal (X : Mat n) (hX : X ∈ algebra n) :
    (∀ t, ∃ u, diagonal n t * X - X * diagonal n t = diagonal n u) ↔
      ∃ t, X = diagonal n t := by
  constructor
  · intro hn
    apply (zero_space X).mp
    refine ⟨hX, fun t => ?_⟩
    obtain ⟨u, hu⟩ := hn t
    have hu0 : u = 0 := by
      funext i
      have hh := congrFun (congrFun hu (Sum.inl i)) (Sum.inl i)
      rw [diagonal_bracket_entry] at hh
      simpa [diagonal] using hh.symm
    rw [hu, hu0]
    simp [diagonal]
  · intro hx
    have hz := (zero_space X).mpr hx
    intro t
    refine ⟨0, ?_⟩
    simpa [diagonal] using hz.2 t

/-- Each nonzero root space has complex dimension one. -/
theorem root_space_finrank (α : Dual n) (ha : α ∈ roots n) :
    Module.finrank ℂ (weightSpace n α) = 1 := by
  obtain ⟨i, j, hij, rfl | rfl | rfl⟩ := (roots_iff α).mp ha
  · rw [difference_space i j hij]; exact finrank_span_singleton (aVector_ne_zero i j)
  · rw [sum_space i j hij]; exact finrank_span_singleton (bVector_ne_zero i j hij)
  · rw [neg_sum_space i j hij]; exact finrank_span_singleton (cVector_ne_zero i j hij)

/-- The table written with i<j and all four independent signs. -/
theorem roots_ordered (α : Dual n) : α ∈ roots n ↔
    ∃ i j : Fin n, i < j ∧
      (α = epsilon n i - epsilon n j ∨ α = -(epsilon n i - epsilon n j) ∨
       α = epsilon n i + epsilon n j ∨ α = -(epsilon n i + epsilon n j)) := by
  rw [roots_iff]
  constructor
  · rintro ⟨i, j, hij, ha⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, hlt, ha.imp_right Or.inr⟩
    · refine ⟨j, i, hgt, ?_⟩
      rcases ha with ha | ha | ha
      · exact Or.inr (Or.inl (ha.trans (by abel)))
      · exact Or.inr (Or.inr (Or.inl (ha.trans (add_comm _ _))))
      · exact Or.inr (Or.inr (Or.inr (ha.trans (congrArg Neg.neg (add_comm _ _)))))
  · rintro ⟨i, j, hij, ha | ha | ha | ha⟩
    · exact ⟨i, j, ne_of_lt hij, Or.inl ha⟩
    · exact ⟨j, i, ne_of_gt hij, Or.inl (ha.trans (by abel))⟩
    · exact ⟨i, j, ne_of_lt hij, Or.inr (Or.inl ha)⟩
    · exact ⟨i, j, ne_of_lt hij, Or.inr (Or.inr ha)⟩

@[simp] theorem dot_coordinate (i j : Fin n) :
    dot n (coordinate n i) (coordinate n j) = if i = j then 1 else 0 := by
  simp [dot, coordinate, Pi.single_apply, ite_and, eq_comm]

theorem root_lengths (i j : Fin n) (hij : i ≠ j) :
    dot n (coordinate n i - coordinate n j) (coordinate n i - coordinate n j) = 2 ∧
    dot n (coordinate n i + coordinate n j) (coordinate n i + coordinate n j) = 2 := by
  have hsub : ∀ a b c d : Params n,
      dot n (a - b) (c - d) = dot n a c - dot n a d - dot n b c + dot n b d := by
    intros; simp [dot, sub_mul, mul_sub, Finset.sum_sub_distrib]; ring
  have hadd : ∀ a b c d : Params n,
      dot n (a + b) (c + d) = dot n a c + dot n a d + dot n b c + dot n b d := by
    intros; simp [dot, add_mul, mul_add, Finset.sum_add_distrib]; ring
  norm_num [hsub, hadd, hij, Ne.symm hij]

/-- The Euclidean normalization specializes to H_i-H_j and H_i+H_j. -/
theorem coroots (i j : Fin n) (hij : i ≠ j) :
    coroot n (coordinate n i - coordinate n j) = diagonal n (coordinate n i - coordinate n j) ∧
    coroot n (coordinate n i + coordinate n j) = diagonal n (coordinate n i + coordinate n j) := by
  simp [coroot, (root_lengths i j hij).1, (root_lengths i j hij).2]

theorem negative_coroot (a : Params n) : coroot n (-a) = -coroot n a := by
  have hd : dot n (-a) (-a) = dot n a a := by simp [dot]
  simp only [coroot, hd, smul_neg]
  ext x y
  cases x <;> cases y <;> simp [diagonal, Matrix.diagonal_apply]
  all_goals split_ifs <;> simp_all

@[simp] theorem diagonal_add (t u : Params n) : diagonal n (t + u) = diagonal n t + diagonal n u := by
  ext a b
  cases a <;> cases b <;> simp [diagonal, Matrix.diagonal_apply, add_ite, ite_add]
  all_goals split_ifs <;> simp_all <;> ring

@[simp] theorem diagonal_sub (t u : Params n) : diagonal n (t - u) = diagonal n t - diagonal n u := by
  ext a b
  cases a <;> cases b <;> simp [diagonal, Matrix.diagonal_apply, sub_ite, ite_sub]
  all_goals split_ifs <;> simp_all <;> ring

@[simp] theorem diagonal_coordinate (i : Fin n) : diagonal n (coordinate n i) = aVector n i i := by
  ext a b
  cases a <;> cases b
  all_goals simp only [diagonal, aVector, coordinate, Matrix.diagonal_apply,
    Matrix.sub_apply, Matrix.single, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Pi.neg_apply, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
    false_and, and_false, ite_false, sub_zero, zero_sub, Pi.single_apply]
  all_goals split_ifs <;> norm_num <;> aesop

/-- Opposite difference root vectors give the Euclidean coroot. -/
theorem difference_bracket (i j : Fin n) (hij : i ≠ j) :
    aVector n i j * aVector n j i - aVector n j i * aVector n i j =
      coroot n (coordinate n i - coordinate n j) := by
  rw [(coroots i j hij).1, diagonal_sub, diagonal_coordinate, diagonal_coordinate]
  simp [aVector, sub_mul, mul_sub, Matrix.single_mul_single_of_ne, hij, Ne.symm hij]
  abel

/-- The opposite of an upper-right skew pair is the *negative* lower-left pair. -/
theorem sum_bracket (i j : Fin n) (hij : i ≠ j) :
    bVector n i j * (-cVector n i j) - (-cVector n i j) * bVector n i j =
      coroot n (coordinate n i + coordinate n j) := by
  rw [(coroots i j hij).2, diagonal_add, diagonal_coordinate, diagonal_coordinate]
  simp [aVector, bVector, cVector, sub_mul, mul_sub, Matrix.single_mul_single_of_ne, hij, Ne.symm hij]
  abel

/-- This confirms that the coordinate identification used in the normalization is the
bilinear Euclidean identification of the displayed epsilon functionals. -/
theorem weight_dot (i j : Fin n) (t : Params n) :
    (epsilon n i - epsilon n j) t = dot n (coordinate n i - coordinate n j) t ∧
    (epsilon n i + epsilon n j) t = dot n (coordinate n i + coordinate n j) t := by
  simp [dot, coordinate, Pi.single_apply, sub_mul, add_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, epsilon]

/-- The negative-sum coroot is obtained by reversing the opposite bracket. -/
theorem neg_sum_bracket (i j : Fin n) (hij : i ≠ j) :
    cVector n i j * (-bVector n i j) - (-bVector n i j) * cVector n i j =
      coroot n (-(coordinate n i + coordinate n j)) := by
  rw [negative_coroot, ← sum_bracket i j hij]
  simp

/-- The normalized opposite vectors satisfy all three sl₂ relations. -/
theorem difference_triple (i j : Fin n) (hij : i ≠ j) :
    let e := aVector n i j
    let f := aVector n j i
    let h := coroot n (coordinate n i - coordinate n j)
    e * f - f * e = h ∧ h * e - e * h = (2 : ℂ) • e ∧
      h * f - f * h = (-2 : ℂ) • f := by
  dsimp only
  refine ⟨difference_bracket i j hij, ?_, ?_⟩
  · rw [(coroots i j hij).1]
    convert (aVector_weight i j).2 (coordinate n i - coordinate n j) using 1 <;>
      norm_num [epsilon, coordinate, Pi.single_apply, hij, Ne.symm hij]
  · rw [(coroots i j hij).1]
    convert (aVector_weight j i).2 (coordinate n i - coordinate n j) using 1 <;>
      norm_num [epsilon, coordinate, Pi.single_apply, hij, Ne.symm hij]

theorem sum_triple (i j : Fin n) (hij : i ≠ j) :
    let e := bVector n i j
    let f := -cVector n i j
    let h := coroot n (coordinate n i + coordinate n j)
    e * f - f * e = h ∧ h * e - e * h = (2 : ℂ) • e ∧
      h * f - f * h = (-2 : ℂ) • f := by
  dsimp only
  refine ⟨sum_bracket i j hij, ?_, ?_⟩
  · rw [(coroots i j hij).2]
    convert (bVector_weight i j).2 (coordinate n i + coordinate n j) using 1 <;>
      norm_num [epsilon, coordinate, Pi.single_apply, hij, Ne.symm hij]
  · rw [(coroots i j hij).2]
    have hc := (cVector_weight i j).2 (coordinate n i + coordinate n j)
    have hc' : diagonal n (coordinate n i + coordinate n j) * cVector n i j -
        cVector n i j * diagonal n (coordinate n i + coordinate n j) = (-2 : ℂ) • cVector n i j := by
      convert hc using 1 <;> norm_num [epsilon, coordinate, Pi.single_apply, hij, Ne.symm hij]
    convert congrArg Neg.neg hc' using 1 <;>
      simp only [Matrix.mul_neg, Matrix.neg_mul, smul_neg] <;> abel

/-- There are no roots in ranks zero and one. -/
theorem roots_empty_of_le_one (hn : n ≤ 1) : roots n = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro α hα
  obtain ⟨i, j, hij, _⟩ := (roots_ordered α).mp hα
  have hij' : i.val < j.val := hij
  have hj := j.isLt
  omega

/-- The rank-zero matrix Lie algebra is the zero algebra. -/
theorem d0_subsingleton : Subsingleton (algebra 0) := by
  constructor
  intro X Y
  apply Subtype.ext
  ext a b
  exact isEmptyElim a

/-- Every element of D₁ is a scalar multiple of the diagonal generator. -/
theorem d1_scalar (X : algebra 1) :
    (X : Mat 1) = (X : Mat 1) (Sum.inl 0) (Sum.inl 0) • aVector 1 0 0 := by
  simpa [Fin.sum_univ_one] using expansion (X : Mat 1) X.property

/-- At rank one the diagonal zero-weight space is the entire algebra. -/
theorem d1_zero_space : weightSpace 1 0 = (algebra 1).toSubmodule := by
  apply le_antisymm
  · exact fun X hX => hX.1
  · intro X hX
    have hgen : aVector 1 0 0 ∈ weightSpace 1 0 := by
      simpa only [sub_self] using aVector_weight (n := 1) 0 0
    have h : X = X (Sum.inl 0) (Sum.inl 0) • aVector 1 0 0 := d1_scalar ⟨X, hX⟩
    have hscalar := (weightSpace 1 0).smul_mem (X (Sum.inl 0) (Sum.inl 0)) hgen
    rwa [← h] at hscalar

theorem d1_finrank : Module.finrank ℂ (algebra 1) = 1 := by
  let e : algebra 1 := ⟨aVector 1 0 0, aVector_mem 0 0⟩
  apply finrank_eq_one e
  · intro h
    exact aVector_ne_zero 0 0 (congrArg Subtype.val h)
  · intro X
    exact ⟨(X : Mat 1) (Sum.inl 0) (Sum.inl 0), Subtype.ext (d1_scalar X).symm⟩

theorem d1_abelian : IsLieAbelian (algebra 1) := by
  constructor
  intro X Y
  apply Subtype.ext
  change (X : Mat 1) * (Y : Mat 1) - (Y : Mat 1) * (X : Mat 1) = 0
  rw [d1_scalar X, d1_scalar Y]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

/-- The excluded low rank is not semisimple in the original, radical-zero sense. -/
theorem d1_not_semisimple :
    ¬ Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ (algebra 1) := by
  letI : IsLieAbelian (algebra 1) := d1_abelian
  intro h
  have ht : (⊤ : LieIdeal ℂ (algebra 1)) = ⊥ := by
    simpa [Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value,
      Specs.LieAlgebrasAndRepresentations.SolvableRadical.radical_value] using h
  let X : algebra 1 := ⟨aVector 1 0 0, aVector_mem 0 0⟩
  have hX : X ∈ (⊥ : LieIdeal ℂ (algebra 1)) := ht ▸ (show X ∈ (⊤ : LieIdeal ℂ (algebra 1)) from trivial)
  have hz : X = 0 := (LieSubmodule.mem_bot _).mp hX
  exact aVector_ne_zero (n := 1) 0 0 (congrArg Subtype.val hz)

end LieAlgebrasAndRepresentations.ClassicalRootsD
