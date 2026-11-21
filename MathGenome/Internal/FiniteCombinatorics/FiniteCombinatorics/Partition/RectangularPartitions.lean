import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Partition.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.RectangularPartitions
import Lean.Elab.Tactic.Omega

noncomputable section
namespace FiniteCombinatorics.Partition

/-- All partitions fitting in the rectangle, in the shared list presentation. -/
abbrev rectangleLists := RectangleSpecs.ListsValue
/-- The integer weight polynomial, with weight the sum of the parts. -/
abbrev F := RectangleSpecs.FValue
/-- Gaussian coefficients, zero for lower indices greater than the upper index. -/
abbrev G := RectangleSpecs.GValue

private theorem admissible_iff (a b : ℕ) (l : List ℕ) :
    RectangleSpecs.Admissible a b l ↔
      l.Pairwise (· ≥ ·) ∧ (∀ i ∈ l, 0 < i) ∧
        l.length ≤ a ∧ ∀ i ∈ l, i ≤ b := by
  constructor
  · rintro ⟨⟨p, hl⟩, ha, hb⟩
    exact ⟨by simpa only [← hl] using p.property.1,
      by simpa only [← hl] using p.property.2.1, ha, hb⟩
  · rintro ⟨hs, hp, ha, hb⟩
    exact ⟨⟨⟨l, hs, hp, rfl⟩, rfl⟩, ha, hb⟩

private theorem admissible_zero_left (b : ℕ) (l : List ℕ) :
    RectangleSpecs.Admissible 0 b l ↔ l = [] := by
  rw [admissible_iff]
  cases l <;> simp

private theorem admissible_zero_right (a : ℕ) (l : List ℕ) :
    RectangleSpecs.Admissible a 0 l ↔ l = [] := by
  rw [admissible_iff]
  cases l with
  | nil => simp
  | cons i l =>
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp,
      List.length_cons, List.cons_ne_nil, iff_false, not_and]
    intro _ hp _ hb
    omega

private theorem admissible_step (a b : ℕ) (l : List ℕ) :
    RectangleSpecs.Admissible (a + 1) (b + 1) l ↔
      RectangleSpecs.Admissible (a + 1) b l ∨
        ∃ t, RectangleSpecs.Admissible a (b + 1) t ∧ (b + 1) :: t = l := by
  simp only [admissible_iff]
  constructor
  · rintro ⟨hs, hp, ha, hb⟩
    by_cases h : ∀ i ∈ l, i ≤ b
    · exact Or.inl ⟨hs, hp, ha, h⟩
    · right
      cases l with
      | nil => simp at h
      | cons i t =>
        have his : ∀ j ∈ t, i ≥ j := (List.pairwise_cons.mp hs).1
        have hi : i = b + 1 := by
          have hib := hb i (by simp)
          by_contra hne
          apply h
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · omega
          · have := his j hj; omega
        subst i
        refine ⟨t, ⟨(List.pairwise_cons.mp hs).2, ?_, ?_, ?_⟩, rfl⟩
        · exact fun j hj => hp j (by simp [hj])
        · simp only [List.length_cons] at ha; omega
        · exact fun j hj => hb j (by simp [hj])
  · rintro (⟨hs, hp, ha, hb⟩ | ⟨t, ⟨hs, hp, ha, hb⟩, rfl⟩)
    · exact ⟨hs, hp, ha, fun j hj => Nat.le_trans (hb j hj) (Nat.le_succ b)⟩
    · refine ⟨List.pairwise_cons.mpr ⟨hb, hs⟩, ?_, ?_, ?_⟩
      · simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by omega, hp⟩
      · simpa using Nat.succ_le_succ ha
      · simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨le_rfl, hb⟩

theorem rectangle_enumeration : RectangleSpecs.Enumeration := by
  intro a b
  induction a, b using RectangleSpecs.ListsValue.induct with
  | case1 b => simp [RectangleSpecs.ListsValue, admissible_zero_left]
  | case2 a => simp [RectangleSpecs.ListsValue, admissible_zero_right]
  | case3 a b ih₁ ih₂ =>
    intro l
    rw [RectangleSpecs.ListsValue]
    simpa only [Finset.mem_union, Finset.mem_image, ih₁, ih₂] using
      (admissible_step a b l).symm

theorem rectangle_finite : RectangleSpecs.FiniteIndex := by
  intro a b
  have he : {l | RectangleSpecs.Admissible a b l} =
      (rectangleLists a b : Set (List ℕ)) := by
    ext l
    exact (rectangle_enumeration a b l).symm
  rw [he]
  exact Finset.finite_toSet _

private theorem rectangle_disjoint (a b : ℕ) :
    Disjoint (rectangleLists (a + 1) b)
      ((rectangleLists a (b + 1)).image (List.cons (b + 1))) := by
  apply Finset.disjoint_left.mpr
  intro l hl hm
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hm
  have h := (rectangle_enumeration _ _ _).mp hl
  have hb := h.2.2 (b + 1) (by simp)
  omega

theorem F_succ_succ (a b : ℕ) :
    F (a + 1) (b + 1) = F (a + 1) b +
      Polynomial.X ^ (b + 1) * F a (b + 1) := by
  unfold F RectangleSpecs.FValue
  rw [RectangleSpecs.ListsValue, Finset.sum_union (rectangle_disjoint a b)]
  congr 1
  rw [Finset.sum_image]
  · simp only [List.sum_cons, pow_add, Finset.mul_sum]
  · intro l _ t _ h
    exact (List.cons.inj h).2

theorem rectangle_recurrence : RectangleSpecs.Recurrence := by
  intro a b ha hb
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  simpa using F_succ_succ a b

theorem rectangle_boundary : RectangleSpecs.Boundary := by
  constructor
  · intro a
    cases a <;> simp [RectangleSpecs.FValue, RectangleSpecs.ListsValue]
  · intro b
    simp [RectangleSpecs.FValue, RectangleSpecs.ListsValue]

@[simp] theorem F_zero_right (a : ℕ) : F a 0 = 1 := rectangle_boundary.1 a
@[simp] theorem F_zero_left (b : ℕ) : F 0 b = 1 := rectangle_boundary.2 b

theorem gaussian_boundary : RectangleSpecs.GaussianBoundary := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simp [RectangleSpecs.GValue, F_zero_left]
  · intro n
    simp [RectangleSpecs.GValue, F_zero_right]
  · intro n k hk
    simp [RectangleSpecs.GValue, Nat.not_le.mpr hk]

theorem gaussian_recurrence : RectangleSpecs.GaussianRecurrence := by
  intro n k
  rcases lt_trichotomy k n with hk | rfl | hk
  · have h₁ : k + 1 ≤ n + 1 := by omega
    have h₂ : k + 1 ≤ n := by omega
    have h₃ : k ≤ n := by omega
    have h₄ : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
    have h₅ : n - k = (n - (k + 1)) + 1 := by omega
    simp only [RectangleSpecs.GValue, ite_eq_left h₁, ite_eq_left h₂, ite_eq_left h₃]
    rw [h₄, h₅]
    exact F_succ_succ k (n - (k + 1))
  · simp [RectangleSpecs.GValue, F_zero_right]
  · have h₁ : ¬k + 1 ≤ n + 1 := by omega
    have h₂ : ¬k + 1 ≤ n := by omega
    have h₃ : ¬k ≤ n := by omega
    simp [RectangleSpecs.GValue, h₁, h₂, h₃]

end FiniteCombinatorics.Partition
