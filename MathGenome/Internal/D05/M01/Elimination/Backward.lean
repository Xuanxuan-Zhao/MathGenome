import MathGenome.Internal.Specs.D05.M01.Elimination.Backward
import MathGenome.Internal.D05.M01.Echelon
import MathGenome.Internal.D05.M01.RowOps

/-! The finite backward pass: normalize one pivot and clear its column above it,
working from the bottom row upward. -/
namespace D05.M01.Elimination.Backward

universe u
open RowOps
variable {K : Type u} [Field K] {m n : ℕ}

/-- Equality of ordered pivot positions. -/
def SamePivots (A B : Matrix (Fin m) (Fin n) K) : Prop :=
  ∀ i c, B.IsLeadingEntry i c ↔ A.IsLeadingEntry i c

/-- A normalized column with zero entries away from its pivot row. -/
def GoodColumn (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (c : Fin n) : Prop :=
  A i c = 1 ∧ ∀ k, k ≠ i → A k c = 0

private theorem samePivots_of_forward (A B : Matrix (Fin m) (Fin n) K)
    (hp : ∀ i c, A.IsLeadingEntry i c → B.IsLeadingEntry i c)
    (hz : ∀ i, A i = 0 → B i = 0) : SamePivots A B := by
  intro i c
  refine ⟨?_, hp i c⟩
  intro hc
  have hA : A i ≠ 0 := fun h => hc.row_ne_zero (hz i h)
  obtain ⟨d, hd⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp hA
  have hdc := (hp i d hd).unique hc
  simpa only [hdc] using hd

private theorem echelon_of_samePivots {A B : Matrix (Fin m) (Fin n) K}
    (hA : A.IsRowEchelon) (hp : SamePivots A B) : B.IsRowEchelon := by
  apply (Echelon.rowEchelon_iff B).mpr
  obtain ⟨hz, ho⟩ := (Echelon.rowEchelon_iff A).mp hA
  have hzero : ∀ i, B i = 0 ↔ A i = 0 := by
    intro i
    constructor <;> intro h <;> by_contra hn
    · obtain ⟨c, hc⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp hn
      exact ((hp i c).mpr hc).row_ne_zero h
    · obtain ⟨c, hc⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp hn
      exact ((hp i c).mp hc).row_ne_zero h
  exact ⟨fun i k hik hi => (hzero k).mpr (hz i k hik ((hzero i).mp hi)),
    fun i k c d hik hc hd => ho i k c d hik ((hp i c).mp hc) ((hp k d).mp hd)⟩

/-- Nonzero scaling preserves every pivot position. -/
theorem scale_samePivots (A : Matrix (Fin m) (Fin n) K)
    (i : Fin m) (a : K) (ha : a ≠ 0) :
    SamePivots A (applyOp (.scale i a ha) A) := by
  intro r c
  by_cases hr : r = i
  · subst r
    simp [Matrix.IsLeadingEntry, applyOp, ha]
  · simp only [Matrix.IsLeadingEntry, applyOp, ite_eq_right hr]

/-- Adding a later echelon row to an earlier row preserves every pivot position. -/
theorem add_later_samePivots (A : Matrix (Fin m) (Fin n) K)
    (he : A.IsRowEchelon) (k i : Fin m) (hki : k < i) (a : K) :
    SamePivots A (applyOp (.add k i a (ne_of_lt hki)) A) := by
  apply samePivots_of_forward
  · intro r c hc
    by_cases hr : r = k
    · subst r
      have hz : ∀ j, j ≤ c → A i j = 0 := by
        intro j hj
        exact he hki (fun d hd => hc.1 d (lt_of_lt_of_le hd hj))
      constructor
      · intro j hj
        simp only [applyOp, ite_eq_left, hc.1 j hj, hz j (le_of_lt hj), mul_zero, add_zero]
      · simpa only [applyOp, ite_eq_left, hz c le_rfl, mul_zero, add_zero] using hc.2
    · simpa only [Matrix.IsLeadingEntry, applyOp, ite_eq_right hr] using hc
  · intro r hrz
    by_cases hr : r = k
    · subst r
      have hi := he.row_eq_zero_of_lt hki hrz
      funext c
      simp only [applyOp, ite_eq_left, congrFun hrz c, congrFun hi c,
        Pi.zero_apply, mul_zero, add_zero]
    · funext c
      simpa only [applyOp, ite_eq_right hr, Pi.zero_apply] using congrFun hrz c

@[simp] theorem applyOperations_nil (A : Matrix (Fin m) (Fin n) K) :
    applyOperations [] A = A := rfl

@[simp] theorem applyOperations_cons (op : RowOperation K m) (ops : List (RowOperation K m))
    (A : Matrix (Fin m) (Fin n) K) :
    applyOperations (op :: ops) A = applyOperations ops (applyOp op A) := rfl

theorem applyOperations_append (ops more : List (RowOperation K m))
    (A : Matrix (Fin m) (Fin n) K) :
    applyOperations (ops ++ more) A = applyOperations more (applyOperations ops A) := by
  exact List.foldl_append

/-- Clear any finite set of rows above a normalized pivot. Columns where the
pivot row vanishes and every row at or below that pivot remain unchanged. -/
theorem clearAbove (A : Matrix (Fin m) (Fin n) K) (he : A.IsRowEchelon)
    (i : Fin m) (c : Fin n) (hi : A i c = 1)
    (s : Finset (Fin m)) (hs : ∀ k ∈ s, k < i) :
    ∃ ops : List (RowOperation K m),
      let B := applyOperations ops A
      SamePivots A B ∧ B.IsRowEchelon ∧ B i c = 1 ∧
      (∀ k ∈ s, B k c = 0) ∧
      (∀ d, A i d = 0 → ∀ r, B r d = A r d) ∧
      (∀ r, i ≤ r → B r = A r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨[], (fun _ _ => Iff.rfl), he, hi, ?_, ?_, ?_⟩
    · simp
    · intros; rfl
    · intros; rfl
  | @insert k s hks ih =>
    have hki := hs k (Finset.mem_insert_self k s)
    obtain ⟨ops, hp, hb, hbi, hz, hcol, hrow⟩ :=
      ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
    let B := applyOperations ops A
    let op : RowOperation K m := .add k i (-B k c) (ne_of_lt hki)
    have hp' : SamePivots B (applyOp op B) := add_later_samePivots B hb k i hki _
    have he' := echelon_of_samePivots hb hp'
    refine ⟨ops ++ [op], ?_⟩
    simp only [applyOperations_append, applyOperations_cons, applyOperations_nil]
    refine ⟨(fun r d => (hp' r d).trans (hp r d)), he', ?_, ?_, ?_, ?_⟩
    · simpa only [op, applyOp, ite_eq_right (ne_of_lt hki).symm] using hbi
    · intro r hr
      rcases Finset.mem_insert.mp hr with hr | hr
      · subst r
        simp only [op, applyOp, ite_eq_left]
        change B k c + (-B k c) * B i c = 0
        rw [show B i c = 1 from hbi, mul_one, add_neg_cancel]
      · have hrk : r ≠ k := fun h => hks (h ▸ hr)
        simpa only [op, applyOp, ite_eq_right hrk] using hz r hr
    · intro d hd r
      have hid : B i d = 0 := by rw [show B i = A i from hrow i le_rfl]; exact hd
      by_cases hrk : r = k
      · subst r
        simp only [op, applyOp, ite_eq_left]
        change B k d + (-B k c) * B i d = A k d
        rw [hid, mul_zero, add_zero]
        exact hcol d hd k
      · simpa only [op, applyOp, ite_eq_right hrk] using hcol d hd r
    · intro r hir
      have hrk : r ≠ k := by intro h; subst r; exact (not_le_of_gt hki) hir
      funext d
      simpa only [op, applyOp, ite_eq_right hrk] using congrFun (hrow r hir) d

/-- Process one row, preserving every already reduced later pivot column. -/
theorem reduceRow (A : Matrix (Fin m) (Fin n) K) (he : A.IsRowEchelon)
    (i : Fin m)
    (hg : ∀ r c, i < r → A.IsLeadingEntry r c → GoodColumn A r c) :
    ∃ ops : List (RowOperation K m),
      let B := applyOperations ops A
      SamePivots A B ∧ B.IsRowEchelon ∧
      ∀ r c, i ≤ r → B.IsLeadingEntry r c → GoodColumn B r c := by
  classical
  by_cases hpi : ∃ c, A.IsLeadingEntry i c
  · obtain ⟨c, hc⟩ := hpi
    let op : RowOperation K m := .scale i (A i c)⁻¹ (inv_ne_zero hc.2)
    let C := applyOp op A
    have hp : SamePivots A C := scale_samePivots A i _ _
    have heC : C.IsRowEchelon := echelon_of_samePivots he hp
    have hiC : C i c = 1 := by
      simp only [C, op, applyOp, ite_eq_left]
      exact inv_mul_cancel₀ hc.2
    obtain ⟨ops, hpD, heD, hiD, hzD, hcolD, hrowD⟩ :=
      clearAbove C heC i c hiC (Finset.univ.filter (· < i)) (by simp)
    let D := applyOperations ops C
    have hpAD : SamePivots A D := fun r d => (hpD r d).trans (hp r d)
    refine ⟨op :: ops, hpAD, heD, ?_⟩
    change ∀ r d, i ≤ r → D.IsLeadingEntry r d → GoodColumn D r d
    intro r d hir hrd
    by_cases hri : r = i
    · subst r
      have hdc : d = c := ((hpAD i d).mp hrd).unique hc
      subst d
      refine ⟨hiD, ?_⟩
      intro k hki
      rcases lt_or_gt_of_ne hki with hki | hik
      · exact hzD k (by simp [hki])
      · exact heD hik hrd.1
    · have hir' : i < r := lt_of_le_of_ne hir (Ne.symm hri)
      have hgA := hg r d hir' ((hpAD r d).mp hrd)
      have hid : A i d = 0 := hgA.2 i (Ne.symm hri)
      have hCd : ∀ k, C k d = A k d := by
        intro k
        by_cases hki : k = i
        · subst k
          simp only [C, op, applyOp, ite_eq_left]
          rw [hid, mul_zero]
        · exact ite_eq_right hki
      have hiCd : C i d = 0 := (hCd i).trans hid
      have hDd : ∀ k, D k d = A k d := fun k => (hcolD d hiCd k).trans (hCd k)
      exact ⟨(hDd r).trans hgA.1, fun k hkr => (hDd k).trans (hgA.2 k hkr)⟩
  · refine ⟨[], (fun _ _ => Iff.rfl), he, ?_⟩
    intro r c hir hc
    by_cases hri : r = i
    · subst r
      exact (hpi ⟨c, hc⟩).elim
    · exact hg r c (lt_of_le_of_ne hir (Ne.symm hri)) hc

/-- A suffix of reduced pivot columns can be extended upward until no rows remain.
The natural number recursion supplies termination even when there are no pivots. -/
theorem reduceSuffix (t : ℕ) (ht : t ≤ m)
    (A : Matrix (Fin m) (Fin n) K) (he : A.IsRowEchelon)
    (hg : ∀ r c, t ≤ r.val → A.IsLeadingEntry r c → GoodColumn A r c) :
    ∃ ops : List (RowOperation K m),
      (applyOperations ops A).IsReducedRowEchelon ∧ SamePivots A (applyOperations ops A) := by
  induction t generalizing A with
  | zero =>
    refine ⟨[], ?_, fun _ _ => Iff.rfl⟩
    apply (Echelon.reducedRowEchelon_iff A).mpr
    exact ⟨he, fun i c hc => hg i c (Nat.zero_le _) hc⟩
  | succ t ih =>
    let i : Fin m := ⟨t, by omega⟩
    obtain ⟨ops, hp, heB, hgB⟩ := reduceRow A he i (by
      intro r c hir hc
      exact hg r c (by change t < r.val at hir; omega) hc)
    let B := applyOperations ops A
    obtain ⟨more, hred, hp'⟩ := ih (by omega) B heB (by
      intro r c htr hc
      exact hgB r c (by exact htr) hc)
    refine ⟨ops ++ more, ?_, ?_⟩
    · simpa only [applyOperations_append] using hred
    · intro r c
      simpa only [applyOperations_append] using (hp' r c).trans (hp r c)

/-- Backward Gauss–Jordan elimination for every finite echelon matrix. -/
theorem exists_reduced_same_pivots : BackwardSpec.exists_reduced_same_pivots := by
  intro K _ m n A he
  exact reduceSuffix m le_rfl A he (by
    intro r c hr
    exact (Nat.not_le_of_gt r.isLt hr).elim)

/-- An entirely pivot-free matrix needs no operations. -/
theorem no_pivots_reduced : BackwardSpec.no_pivots_reduced := by
  intro K _ m n A hp
  have hz : A = 0 := by
    apply Matrix.ext
    intro i c
    by_contra h
    have hi : A i ≠ 0 := fun hi => h (congrFun hi c)
    obtain ⟨d, hd⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp hi
    exact hp i d hd
  rw [applyOperations_nil, hz]
  exact Echelon.zero_forms.2

theorem empty_rows_reduced : BackwardSpec.empty_rows_reduced := by
  intro K _ n A
  exact (Echelon.empty_rows_forms A).2

theorem empty_columns_reduced : BackwardSpec.empty_columns_reduced := by
  intro K _ m A
  exact (Echelon.empty_columns_forms A).2

end D05.M01.Elimination.Backward
