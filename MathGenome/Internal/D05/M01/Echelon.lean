import MathGenome.Internal.Specs.D05.M01.Echelon
import MathGenome.Internal.D05.M01.System

/-! Echelon predicates and their ordered-pivot interpretation, K05.01.echelon. -/
namespace D05.M01.Echelon

universe u

/-- The first nonzero entry in the indicated row. -/
def IsPivot {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (c : Fin n) : Prop :=
  A.IsLeadingEntry i c

/-- The canonical Mathlib row-echelon predicate on ordered finite indices. -/
def IsRowEchelon {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) : Prop := A.IsRowEchelon

/-- The canonical reduced predicate, retaining the rightmost column if augmented. -/
def IsReducedRowEchelon {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) : Prop := A.IsReducedRowEchelon

variable {K : Type u} [Field K] {m n : ℕ}

theorem pivot_iff (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (c : Fin n) :
    IsPivot A i c ↔ (∀ j, j < c → A i j = 0) ∧ A i c ≠ 0 := Iff.rfl

theorem exists_pivot_iff (A : Matrix (Fin m) (Fin n) K) (i : Fin m) :
    (∃ c, IsPivot A i c) ↔ A i ≠ 0 :=
  Matrix.row_ne_zero_iff_exists_isLeadingEntry.symm

theorem pivot_unique (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (c d : Fin n)
    (hc : IsPivot A i c) (hd : IsPivot A i d) : c = d := hc.unique hd

theorem rowEchelon_iff (A : Matrix (Fin m) (Fin n) K) :
    IsRowEchelon A ↔
      (∀ i k, i < k → A i = 0 → A k = 0) ∧
      (∀ i k c d, i < k → IsPivot A i c → IsPivot A k d → c < d) := by
  constructor
  · intro h
    refine ⟨fun _ _ hik hi => h.row_eq_zero_of_lt hik hi, ?_⟩
    intro i k c d hik hc hd
    by_contra hcd
    exact hd.2 (h hik fun j hj => hc.1 j (lt_of_lt_of_le hj (le_of_not_gt hcd)))
  · rintro ⟨hz, hp⟩ i k hik j hj
    by_cases hi : A i = 0
    · exact congrFun (hz i k hik hi) j
    by_cases hk : A k = 0
    · exact congrFun hk j
    obtain ⟨c, hc⟩ := (exists_pivot_iff A i).mpr hi
    obtain ⟨d, hd⟩ := (exists_pivot_iff A k).mpr hk
    have hcd := hp i k c d hik hc hd
    have hjc : j ≤ c := le_of_not_gt (fun hcj => hc.2 (hj c hcj))
    exact hd.1 j (lt_of_le_of_lt hjc hcd)

/-- Strict increase for adjacent nonzero rows propagates through the nonzero prefix. -/
theorem rowEchelon_iff_consecutive (A : Matrix (Fin m) (Fin n) K) :
    IsRowEchelon A ↔
      (∀ i k, i < k → A i = 0 → A k = 0) ∧
      (∀ i k c d, k.val = i.val + 1 → IsPivot A i c → IsPivot A k d → c < d) := by
  constructor
  · intro h
    obtain ⟨hz, hp⟩ := (rowEchelon_iff A).mp h
    refine ⟨hz, ?_⟩
    intro i k c d hik hc hd
    exact hp i k c d (by omega) hc hd
  · rintro ⟨hz, hs⟩
    apply (rowEchelon_iff A).mpr
    refine ⟨hz, ?_⟩
    intro i k c d hik hc hd
    have hp : ∀ t : ℕ, ∀ k : Fin m, k.val = t → i < k →
        ∀ d, IsPivot A k d → c < d := by
      intro t
      induction t with
      | zero =>
        intro k hk hik
        have : k.val = 0 := hk
        have : i.val < k.val := hik
        omega
      | succ t ih =>
        intro k hk hik d hd
        by_cases hti : t = i.val
        · exact hs i k c d (by omega) hc hd
        · have ht : t < m := by omega
          let p : Fin m := ⟨t, ht⟩
          have hip : i < p := by change i.val < t; omega
          have hpk : p < k := by change t < k.val; omega
          have hpne : A p ≠ 0 := by
            intro hpz
            exact hd.row_ne_zero (hz p k hpk hpz)
          obtain ⟨e, he⟩ := (exists_pivot_iff A p).mpr hpne
          exact lt_trans (ih p rfl hip e he) (hs p k e d (by change k.val = t + 1; omega) he hd)
    exact hp k.val k rfl hik d hd

theorem below_pivot_zero (A : Matrix (Fin m) (Fin n) K) (h : IsRowEchelon A)
    (i k : Fin m) (c : Fin n) (hik : i < k) (hc : IsPivot A i c) : A k c = 0 :=
  h hik hc.1

theorem reducedRowEchelon_iff (A : Matrix (Fin m) (Fin n) K) :
    IsReducedRowEchelon A ↔ IsRowEchelon A ∧
      ∀ i c, IsPivot A i c → A i c = 1 ∧ ∀ k, k ≠ i → A k c = 0 := by
  constructor
  · intro h
    exact ⟨h.isRowEchelon, fun _ _ hc =>
      ⟨h.eq_one hc, fun _ hki => h.eq_zero_of_ne_of_isLeadingEntry hki hc⟩⟩
  · rintro ⟨he, hp⟩
    refine ⟨he, ?_, ?_⟩
    · intro i c hc
      exact (hp i c hc).1
    · intro i k c hik hc
      exact (hp k c hc).2 i (ne_of_lt hik)

theorem reduced_isRowEchelon (A : Matrix (Fin m) (Fin n) K)
    (h : IsReducedRowEchelon A) : IsRowEchelon A := h.isRowEchelon

theorem zero_forms :
    IsRowEchelon (0 : Matrix (Fin m) (Fin n) K) ∧
    IsReducedRowEchelon (0 : Matrix (Fin m) (Fin n) K) := by
  have he : IsRowEchelon (0 : Matrix (Fin m) (Fin n) K) := fun _ _ _ _ _ => rfl
  refine ⟨he, (reducedRowEchelon_iff _).mpr ⟨he, ?_⟩⟩
  intro i c hc
  exact (hc.2 rfl).elim

theorem empty_rows_forms (A : Matrix (Fin 0) (Fin n) K) :
    IsRowEchelon A ∧ IsReducedRowEchelon A := by
  have hA : A = 0 := Subsingleton.elim _ _
  rw [hA]
  exact zero_forms

theorem empty_columns_forms (A : Matrix (Fin m) (Fin 0) K) :
    IsRowEchelon A ∧ IsReducedRowEchelon A := by
  have hA : A = 0 := Subsingleton.elim _ _
  rw [hA]
  exact zero_forms

theorem augmented_pivot_last_iff (A : Matrix (Fin m) (Fin n) K)
    (b : Fin m → K) (i : Fin m) :
    IsPivot (System.augmentedMatrix A b) i (Fin.last n) ↔ A i = 0 ∧ b i ≠ 0 := by
  rw [pivot_iff]
  constructor
  · rintro ⟨hz, hb⟩
    refine ⟨?_, ?_⟩
    · funext j
      simpa only [System.augmentedMatrix_castSucc, Pi.zero_apply] using
        hz j.castSucc (Fin.castSucc_lt_last j)
    · simpa only [System.augmentedMatrix_last] using hb
  · rintro ⟨hA, hb⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      revert hj
      refine Fin.lastCases ?_ (fun c => ?_) j
      · intro hj
        exact (lt_irrefl _ hj).elim
      · intro _
        rw [System.augmentedMatrix_castSucc]
        exact congrFun hA c
    · simpa only [System.augmentedMatrix_last] using hb

theorem last_pivot_no_solution (A : Matrix (Fin m) (Fin n) K)
    (b : Fin m → K) (i : Fin m)
    (h : IsPivot (System.augmentedMatrix A b) i (Fin.last n)) :
    ¬ ∃ x, System.IsSolution A b x := by
  obtain ⟨hz, hb⟩ := (augmented_pivot_last_iff A b i).mp h
  rintro ⟨x, hx⟩
  have hi := (System.solution_iff_rows A b x).mp hx i
  have hij : ∀ j, A i j = 0 := fun j => congrFun hz j
  simp only [hij, zero_mul, Finset.sum_const_zero] at hi
  exact hb hi.symm

end D05.M01.Echelon
