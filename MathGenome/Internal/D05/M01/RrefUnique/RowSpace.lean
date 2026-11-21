import MathGenome.Internal.Specs.D05.M01.RrefUnique.RowSpace
import MathGenome.Internal.D05.M01.Echelon
import MathGenome.Internal.D05.M01.RowOps
import MathGenome.Internal.D05.M02.Span

/-! Row-space invariants and uniqueness of reduced row-echelon matrices.
No elimination algorithm or uniqueness certificate is used. -/
namespace D05.M01.RrefUnique.RowSpace

universe u
open scoped BigOperators
open D05.M01

/-- The algebraic span of the indexed rows of a matrix. -/
abbrev rowSpace {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) : Submodule K (Fin n → K) :=
  Submodule.span K (Set.range A)

variable {K : Type u} [Field K] {m n : ℕ}

lemma row_mem_rowSpace (A : Matrix (Fin m) (Fin n) K) (i : Fin m) :
    A i ∈ rowSpace A := Submodule.subset_span ⟨i, rfl⟩

/-- A reduced pivot column reads off the coefficient of its row in any combination. -/
lemma combination_pivot (R : Matrix (Fin m) (Fin n) K)
    (hR : Echelon.IsReducedRowEchelon R) (a : Fin m → K)
    {i : Fin m} {c : Fin n} (hc : Echelon.IsPivot R i c) :
    (∑ k, a k • R k) c = a i := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [hR.eq_one hc, mul_one]
  · intro k _ hki
    rw [hR.eq_zero_of_ne_of_isLeadingEntry hki hc, mul_zero]
  · simp

theorem zero_of_pivot_coordinates (R : Matrix (Fin m) (Fin n) K)
    (hR : Echelon.IsReducedRowEchelon R) (x : Fin n → K)
    (hx : x ∈ rowSpace R)
    (hz : ∀ i c, Echelon.IsPivot R i c → x c = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : R i = 0
  · rw [hi, smul_zero]
  · obtain ⟨c, hc⟩ := (Echelon.exists_pivot_iff R i).mpr hi
    have ha : a i = 0 := (combination_pivot R hR a hc).symm.trans (hz i c hc)
    rw [ha, zero_smul]

theorem leading_columns_iff (R : Matrix (Fin m) (Fin n) K)
    (hR : Echelon.IsReducedRowEchelon R) (c : Fin n) :
    (∃ x ∈ rowSpace R, (∀ j, j < c → x j = 0) ∧ x c ≠ 0) ↔
      ∃ i, Echelon.IsPivot R i c := by
  constructor
  · rintro ⟨x, hx, hbefore, hnonzero⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    by_contra hnone
    apply hnonzero
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : R i = 0
    · simp [hi]
    obtain ⟨d, hd⟩ := (Echelon.exists_pivot_iff R i).mpr hi
    have hdc : d ≠ c := fun heq => hnone ⟨i, heq ▸ hd⟩
    rcases lt_or_gt_of_ne hdc with hlt | hgt
    · have ha : a i = 0 :=
        (combination_pivot R hR a hd).symm.trans (hbefore d hlt)
      rw [ha, zero_mul]
    · rw [hd.1 c hgt, mul_zero]
  · rintro ⟨i, hi⟩
    exact ⟨R i, row_mem_rowSpace R i, hi⟩

/-- Comparison of row indices agrees with comparison of their leading columns. -/
lemma pivot_row_lt_iff (A : Matrix (Fin m) (Fin n) K)
    (hA : Echelon.IsRowEchelon A) {i k : Fin m} {c d : Fin n}
    (hc : Echelon.IsPivot A i c) (hd : Echelon.IsPivot A k d) :
    i < k ↔ c < d := by
  have hp := (Echelon.rowEchelon_iff A).mp hA |>.2
  constructor
  · exact fun hik => hp i k c d hik hc hd
  · intro hcd
    rcases lt_trichotomy i k with hik | hik | hik
    · exact hik
    · subst k
      exact (ne_of_lt hcd (hc.unique hd)).elim
    · exact (lt_asymm hcd (hp k i d c hik hd hc)).elim

/-- Inclusion of pivot sets forces the corresponding pivot in the other matrix
not to occur earlier. Strong induction counts preceding rows without a rank API. -/
lemma pivot_index_le (R S : Matrix (Fin m) (Fin n) K)
    (hR : Echelon.IsRowEchelon R) (hS : Echelon.IsRowEchelon S)
    (hp : ∀ c, (∃ i, Echelon.IsPivot R i c) → ∃ k, Echelon.IsPivot S k c)
    {i k : Fin m} {c : Fin n}
    (hc : Echelon.IsPivot R i c) (hd : Echelon.IsPivot S k c) : i ≤ k := by
  have aux : ∀ t : ℕ, ∀ i : Fin m, i.val = t → ∀ k c,
      Echelon.IsPivot R i c → Echelon.IsPivot S k c → i ≤ k := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro i hit k c hic hkc
      by_contra hn
      have hki : k < i := lt_of_not_ge hn
      have hRk : R k ≠ 0 := by
        intro hz
        exact hic.row_ne_zero (hR.row_eq_zero_of_lt hki hz)
      obtain ⟨d, hkd⟩ := (Echelon.exists_pivot_iff R k).mpr hRk
      have hdc : d < c := (pivot_row_lt_iff R hR hkd hic).mp hki
      obtain ⟨l, hld⟩ := hp d ⟨k, hkd⟩
      have hlk : l < k := (pivot_row_lt_iff S hS hld hkc).mpr hdc
      have hkl : k ≤ l := ih k.val (by omega) k rfl l d hkd hld
      exact (not_lt_of_ge hkl) hlk
  exact aux i.val i rfl k c hc hd

lemma pivot_columns_iff (R S : Matrix (Fin m) (Fin n) K)
    (hR : Echelon.IsReducedRowEchelon R) (hS : Echelon.IsReducedRowEchelon S)
    (hspan : rowSpace R = rowSpace S) (c : Fin n) :
    (∃ i, Echelon.IsPivot R i c) ↔ ∃ i, Echelon.IsPivot S i c := by
  rw [← leading_columns_iff R hR, ← leading_columns_iff S hS, hspan]

theorem ordered_pivots_iff (R S : Matrix (Fin m) (Fin n) K)
    (hR : Echelon.IsReducedRowEchelon R) (hS : Echelon.IsReducedRowEchelon S)
    (hspan : rowSpace R = rowSpace S) (i : Fin m) (c : Fin n) :
    Echelon.IsPivot R i c ↔ Echelon.IsPivot S i c := by
  have hp := pivot_columns_iff R S hR hS hspan
  have forward : ∀ (A B : Matrix (Fin m) (Fin n) K),
      Echelon.IsRowEchelon A → Echelon.IsRowEchelon B →
      (∀ d, (∃ j, Echelon.IsPivot A j d) ↔ ∃ j, Echelon.IsPivot B j d) →
      ∀ i c, Echelon.IsPivot A i c → Echelon.IsPivot B i c := by
    intro A B hA hB hp i c hic
    obtain ⟨k, hkc⟩ := (hp c).mp ⟨i, hic⟩
    have hik := pivot_index_le A B hA hB (fun d => (hp d).mp) hic hkc
    have hki := pivot_index_le B A hB hA (fun d => (hp d).mpr) hkc hic
    have heq : k = i := le_antisymm hki hik
    exact heq ▸ hkc
  exact ⟨forward R S hR.isRowEchelon hS.isRowEchelon hp i c,
    forward S R hS.isRowEchelon hR.isRowEchelon (fun d => (hp d).symm) i c⟩

theorem eq_of_rowSpace_eq (R S : Matrix (Fin m) (Fin n) K)
    (hR : Echelon.IsReducedRowEchelon R) (hS : Echelon.IsReducedRowEchelon S)
    (hspan : rowSpace R = rowSpace S) : R = S := by
  have hp := ordered_pivots_iff R S hR hS hspan
  funext i
  apply sub_eq_zero.mp
  apply zero_of_pivot_coordinates R hR
  · apply (rowSpace R).sub_mem (row_mem_rowSpace R i)
    rw [hspan]
    exact row_mem_rowSpace S i
  · intro k c hkc
    have hsc := (hp k c).mp hkc
    change R i c - S i c = 0
    by_cases hik : i = k
    · subst k
      rw [hR.eq_one hkc, hS.eq_one hsc, sub_self]
    · rw [hR.eq_zero_of_ne_of_isLeadingEntry hik hkc,
        hS.eq_zero_of_ne_of_isLeadingEntry hik hsc, sub_self]

lemma rowSpace_applyOp_le (op : RowOps.RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) : rowSpace (RowOps.applyOp op A) ≤ rowSpace A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  cases op with
  | swap i j hij => exact row_mem_rowSpace A (Equiv.swap i j r)
  | scale i a ha =>
    by_cases hr : r = i
    · subst r
      have heq : RowOps.applyOp (.scale i a ha) A i = a • A i := by
        funext c
        simp [RowOps.applyOp, Pi.smul_apply, smul_eq_mul]
      rw [heq]
      exact (rowSpace A).smul_mem a (row_mem_rowSpace A i)
    · have heq : RowOps.applyOp (.scale i a ha) A r = A r := by
        funext c
        simp [RowOps.applyOp, hr]
      rw [heq]
      exact row_mem_rowSpace A r
  | add i j a hij =>
    by_cases hr : r = i
    · subst r
      have heq : RowOps.applyOp (.add i j a hij) A i = A i + a • A j := by
        funext c
        simp [RowOps.applyOp, Pi.smul_apply, smul_eq_mul]
      rw [heq]
      exact (rowSpace A).add_mem (row_mem_rowSpace A i)
        ((rowSpace A).smul_mem a (row_mem_rowSpace A j))
    · have heq : RowOps.applyOp (.add i j a hij) A r = A r := by
        funext c
        simp [RowOps.applyOp, hr]
      rw [heq]
      exact row_mem_rowSpace A r

theorem row_operation_preserves_rowSpace (op : RowOps.RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) : rowSpace (RowOps.applyOp op A) = rowSpace A := by
  apply le_antisymm (rowSpace_applyOp_le op A)
  have h := rowSpace_applyOp_le (RowOps.inverse op) (RowOps.applyOp op A)
  rwa [RowOps.inverse_apply] at h

end D05.M01.RrefUnique.RowSpace
