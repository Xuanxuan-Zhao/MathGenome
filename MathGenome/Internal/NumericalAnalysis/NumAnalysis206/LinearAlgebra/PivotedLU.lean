import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.PivotedLU
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.PivotedLU
open NumAnalysis206.MatrixDefinitions
universe u
variable {K : Type u} [Field K] {m n : ℕ}

@[simp] theorem store_mul (r : Fin m) (ell : Fin m → K) (A : Mat K m n)
    (i : Fin m) (j : Fin n) :
    (store r ell * A) i j = A i j + ell i * A r j := by
  classical
  change (∑ k : Fin m, ((1 : Mat K m m) i k + if k = r then ell i else 0) * A k j) = _
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp [Matrix.one_apply, ite_mul]

@[simp] theorem permutationMatrix_mul (p : Equiv.Perm (Fin m)) (A : Mat K m n) :
    permutationMatrix p * A = permuteRows p A := by
  classical
  ext i j
  simp [permutationMatrix, Matrix.mul_apply, permuteRows]

theorem store_unitLower (r : Fin m) (ell : Fin m → K)
    (hell : ∀ i, i ≤ r → ell i = 0) : IsUnitLowerTriangular (store r ell) := by
  classical
  constructor
  · intro i j hij
    have hne : i ≠ j := by omega
    by_cases hj : j = r
    · subst j
      simp [store, hne, hell i (by omega)]
    · simp [store, hne, hj]
  · intro i
    by_cases hi : i = r
    · subst i; simp [store, hell r le_rfl]
    · simp [store, hi]

theorem unitLower_mul {A B : Mat K m m} (hA : IsUnitLowerTriangular A)
    (hB : IsUnitLowerTriangular B) : IsUnitLowerTriangular (A * B) := by
  classical
  constructor
  · intro i j hij
    change (∑ k : Fin m, A i k * B k j) = 0
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i.val < k.val
    · rw [hA.1 i k hik, zero_mul]
    · rw [hB.1 k j (by omega), mul_zero]
  · intro i
    have hs : (∑ k : Fin m, A i k * B k i) = A i i * B i i := by
      apply Finset.sum_eq_single i
      · intro k _ hki
        rcases lt_or_gt_of_ne hki with h | h
        · rw [hB.1 k i h, mul_zero]
        · rw [hA.1 i k h, zero_mul]
      · simp
    exact hs.trans (by rw [hA.2, hB.2, one_mul])

theorem eliminate_pivot (A : Mat K m n) (r q : Fin m) (d : Fin n)
    (hp : A q d ≠ 0) :
    eliminate A r q d r d = A q d ∧
      ∀ i, r < i → eliminate A r q d i d = 0 := by
  classical
  constructor
  · simp [eliminate, multipliers]
  · intro i hi
    simp [eliminate, multipliers, hi, hp]

theorem eliminate_above (A : Mat K m n) (r q : Fin m) (d : Fin n)
    (hq : r ≤ q) (i : Fin m) (hi : i < r) : eliminate A r q d i = A i := by
  classical
  funext j
  have hiq : i ≠ q := ne_of_lt (lt_of_lt_of_le hi hq)
  simp [eliminate, multipliers, not_lt_of_ge (le_of_lt hi),
    Equiv.swap_apply_of_ne_of_ne (ne_of_lt hi) hiq]

theorem eliminate_lowerZero (A : Mat K m n) (r q : Fin m) (d : Fin n)
    (hq : r ≤ q) (hp : A q d ≠ 0) (hz : LowerZero A r.val d.val) :
    LowerZero (eliminate A r q d) (r.val + 1) (d.val + 1) := by
  classical
  intro i j hi hj
  have hir : r < i := by exact hi
  have hjd : j ≤ d := by exact Nat.lt_succ_iff.mp hj
  rcases hjd.eq_or_lt with h | h
  · subst j
    exact (eliminate_pivot A r q d hp).2 i hir
  · have hs : r ≤ Equiv.swap r q i := by
      by_cases hiq : i = q
      · subst i; simp
      · simp [Equiv.swap_apply_of_ne_of_ne (ne_of_gt hir) hiq]
        exact le_of_lt hir
    simp [eliminate, hz _ _ hs h, hz q j hq h]

theorem eliminate_left (A : Mat K m n) (r q : Fin m) (d : Fin n)
    (hq : r ≤ q) (hz : LowerZero A r.val d.val) (i : Fin m) (j : Fin n)
    (hj : j < d) : eliminate A r q d i j = A i j := by
  by_cases hi : i < r
  · exact congrFun (eliminate_above A r q d hq i hi) j
  · classical
    have hs : r ≤ Equiv.swap r q i := by
      by_cases hir : i = r
      · subst i; simpa using hq
      by_cases hiq : i = q
      · subst i; simp
      · simpa [Equiv.swap_apply_of_ne_of_ne hir hiq] using le_of_not_gt hi
    simp [eliminate, hz _ _ hs hj, hz q j hq hj, hz i j (le_of_not_gt hi) hj]

/-- A pivot stage is inverted by storing exactly its unnormalized multipliers. -/
theorem undo_eliminate (A : Mat K m n) (r q : Fin m) (d : Fin n) :
    store r (multipliers A r q d) * eliminate A r q d =
      permuteRows (Equiv.swap r q) A := by
  classical
  ext i j
  simp [eliminate, multipliers, permuteRows]

/-- Later row exchanges fix every row above their row cursor. -/
theorem Run.fixes {r c : ℕ} {A U : Mat K m n} {p L ps}
    (h : Run r c A p L U ps) : ∀ i : Fin m, i.val < r → p i = i := by
  induction h with
  | stop => intro i _; rfl
  | skip hc hz ht ih => exact ih
  | @pivot r c A p L U ps hr hc q hq hp ht ih =>
    intro i hi
    have hip : p i = i := ih i (by omega)
    have hir : i ≠ (⟨r, hr⟩ : Fin m) := by intro h; have hh : i.val = r := congrArg Fin.val h; omega
    have hiq : i ≠ q := by intro h; subst i; omega
    simp [Equiv.trans_apply, hip, Equiv.swap_apply_of_ne_of_ne hir hiq]

/-- The output factors are justified by the operations, rather than assumed
by the run. The induction permutes stored multipliers at each later swap. -/
theorem Run.factorization {r c : ℕ} {A U : Mat K m n} {p L ps}
    (h : Run r c A p L U ps) :
    IsUnitLowerTriangular L ∧ permuteRows p A = L * U := by
  induction h with
  | stop =>
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j hij
      have : i ≠ j := by omega
      simp [this]
    · intro i; simp
    · rw [Matrix.one_mul]; rfl
  | skip hc hz ht ih => exact ih
  | @pivot r c A p L U ps hr hc q hq hp ht ih =>
    let row : Fin m := ⟨r, hr⟩
    let col : Fin n := ⟨c, hc⟩
    let ell := multipliers A row q col
    have hpr : p row = row := ht.fixes row (by simp [row])
    have hell : ∀ i : Fin m, i ≤ row → ell (p i) = 0 := by
      intro i hi
      rw [ht.fixes i (by change i.val ≤ r at hi; omega)]
      simp [ell, multipliers, not_lt_of_ge hi]
    refine ⟨unitLower_mul (store_unitLower row (fun i => ell (p i)) hell) ih.1, ?_⟩
    have hs : permuteRows p (permuteRows (Equiv.swap row q) A) =
        store row (fun i => ell (p i)) * permuteRows p (eliminate A row q col) := by
      rw [← undo_eliminate A row q col]
      ext i j
      simp [permuteRows, hpr, ell]
    change permuteRows (p.trans (Equiv.swap row q)) A = _
    change permuteRows p (permuteRows (Equiv.swap row q) A) = _
    rw [hs, ih.2, Matrix.mul_assoc]

/-- A finite scan terminates after at most n-c further columns. -/
theorem run_exists (A : Mat K m n) (r c : ℕ) (hz : LowerZero A r c) :
    ∃ p L U ps, Run r c A p L U ps := by
  classical
  have main : ∀ k c r (A : Mat K m n), n - c ≤ k → LowerZero A r c →
      ∃ p L U ps, Run r c A p L U ps := by
    intro k
    induction k with
    | zero =>
      intro c r A hk hz
      refine ⟨_, _, _, _, .stop ?_⟩
      intro i hi j
      exact hz i j hi (by have := j.isLt; omega)
    | succ k ih =>
      intro c r A hk hz
      by_cases hc : c < n
      · by_cases hr : r < m
        · by_cases hcol : ∀ i : Fin m, r ≤ i.val → A i ⟨c, hc⟩ = 0
          · have hz' : LowerZero A r (c + 1) := by
              intro i j hi hj
              by_cases hjc : j.val < c
              · exact hz i j hi hjc
              · have hjEq : j = (⟨c, hc⟩ : Fin n) := Fin.ext (by change j.val = c; omega)
                subst j
                exact hcol i hi
            obtain ⟨p, L, U, ps, ht⟩ := ih (c + 1) r A (by omega) hz'
            exact ⟨p, L, U, ps, .skip hc hcol ht⟩
          · push Not at hcol
            obtain ⟨q, hq, hp⟩ := hcol
            let B := eliminate A ⟨r, hr⟩ q ⟨c, hc⟩
            have hz' : LowerZero B (r + 1) (c + 1) :=
              eliminate_lowerZero A ⟨r, hr⟩ q ⟨c, hc⟩ hq hp hz
            obtain ⟨p, L, U, ps, ht⟩ := ih (c + 1) (r + 1) B (by omega) hz'
            exact ⟨_, _, _, _, .pivot hr hc q hq hp ht⟩
        · refine ⟨_, _, _, _, .stop ?_⟩
          intro i hi
          have := i.isLt
          omega
      · refine ⟨_, _, _, _, .stop ?_⟩
        intro i hi j
        exact hz i j hi (by have := j.isLt; omega)
  exact main (n - c) c r A le_rfl hz

/-- Completed rows are never changed again. -/
theorem Run.preserves_above {r c : ℕ} {A U : Mat K m n} {p L ps}
    (h : Run r c A p L U ps) : ∀ i : Fin m, i.val < r → U i = A i := by
  induction h with
  | stop => intro i _; rfl
  | skip hc hz ht ih => exact ih
  | @pivot r c A p L U ps hr hc q hq hp ht ih =>
    intro i hi
    exact (ih i (by omega)).trans (eliminate_above A ⟨r, hr⟩ q ⟨c, hc⟩ hq i hi)

/-- Pivot count, strictly increasing pivot columns, and the scan's lower bound. -/
theorem Run.bounds {r c : ℕ} {A U : Mat K m n} {p L ps}
    (h : Run r c A p L U ps) (hr : r ≤ m) :
    ps.length ≤ m - r ∧ ps.Pairwise (· < ·) ∧ ∀ d ∈ ps, c ≤ d.val := by
  induction h with
  | stop => simp
  | @skip r c A p L U ps hc hz ht ih =>
    obtain ⟨hlen, hpair, hall⟩ := ih hr
    exact ⟨hlen, hpair, fun d hd => le_trans (Nat.le_succ c) (hall d hd)⟩
  | @pivot r c A p L U ps hrow hc q hq hp ht ih =>
    obtain ⟨hlen, hpair, hall⟩ := ih (by omega)
    refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨fun d hd => (show c < d.val from hall d hd), hpair⟩
    · intro d hd
      rcases List.mem_cons.mp hd with hd | hd
      · subst d; exact le_rfl
      · exact le_trans (Nat.le_succ c) (hall d hd)

/-- The recorded pivots are the actual leading entries of the final rows;
all rows after the pivot prefix vanish. -/
theorem Run.pivots {r c : ℕ} {A U : Mat K m n} {p L ps}
    (h : Run r c A p L U ps) (hz : LowerZero A r c) :
    (∀ t : Fin ps.length, ∃ i : Fin m, i.val = r + t.val ∧
      U i (ps.get t) ≠ 0 ∧ ∀ j, j < ps.get t → U i j = 0) ∧
    (∀ i : Fin m, r + ps.length ≤ i.val → ∀ j, U i j = 0) := by
  induction h with
  | stop hzA => exact ⟨fun t => Fin.elim0 t, by simpa using hzA⟩
  | @skip r c A p L U ps hc hcol ht ih =>
    apply ih
    intro i j hi hj
    by_cases hjc : j.val < c
    · exact hz i j hi hjc
    · have hjEq : j = (⟨c, hc⟩ : Fin n) := Fin.ext (by change j.val = c; omega)
      subst j
      exact hcol i hi
  | @pivot r c A p L U ps hr hc q hq hp ht ih =>
    have hzB := eliminate_lowerZero A ⟨r, hr⟩ q ⟨c, hc⟩ hq hp hz
    obtain ⟨hpiv, hzero⟩ := ih hzB
    have ha := ht.preserves_above
    refine ⟨?_, ?_⟩
    · intro t
      refine Fin.cases ?_ (fun t => ?_) t
      · refine ⟨⟨r, hr⟩, by simp, ?_, ?_⟩
        · change U ⟨r, hr⟩ ⟨c, hc⟩ ≠ 0
          rw [ha ⟨r, hr⟩ (by simp)]
          rw [(eliminate_pivot A ⟨r, hr⟩ q ⟨c, hc⟩ hp).1]
          exact hp
        · intro j hj
          rw [ha ⟨r, hr⟩ (by simp)]
          simp [eliminate, multipliers, hz q j hq hj]
      · obtain ⟨i, hi, hpi, hleft⟩ := hpiv t
        exact ⟨i, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi,
          hpi, hleft⟩
    · intro i hi
      apply hzero i
      simp only [List.length_cons] at hi
      omega

/-- The run's ordered pivot prefix gives the canonical upstream echelon
predicate, with zero rows at the bottom. -/
theorem Run.rowEchelon {A U : Mat K m n} {p L ps}
    (h : Run 0 0 A p L U ps) : IsRowEchelon U := by
  obtain ⟨hlen, hpair, _⟩ := h.bounds (Nat.zero_le m)
  simp only [Nat.sub_zero] at hlen
  obtain ⟨hpiv, hzero⟩ := h.pivots (by intro i j _ hj; omega)
  refine ⟨ps.length, hlen, ps.get, ?_, ?_, ?_⟩
  · intro i j hij
    exact List.pairwise_iff_get.mp hpair i j hij
  · intro t
    obtain ⟨i, hi, hpi, hleft⟩ := hpiv t
    have hieq : i = Fin.castLE hlen t := Fin.ext (by simpa using hi)
    simpa only [← hieq] using And.intro hpi hleft
  · intro i hi
    exact hzero i (by simpa using hi)

/-- Strictly increasing pivot columns put the i-th pivot in column at least i. -/
theorem echelon_upperTriangular {A : Mat K m n} (h : IsRowEchelon A) :
    IsUpperTriangular A := by
  obtain ⟨r, hr, p, hmono, hpiv, hzero⟩ := h
  have hcol : ∀ i : Fin r, i.val ≤ (p i).val := by
    intro i
    have aux : ∀ k, ∀ i : Fin r, i.val = k → k ≤ (p i).val := by
      intro k
      induction k with
      | zero => intro i hi; omega
      | succ k ih =>
        intro i hi
        let t : Fin r := ⟨k, by have := i.isLt; omega⟩
        have ht : t < i := by change k < i.val; omega
        have hlt : (p t).val < (p i).val := hmono ht
        have hle := ih t rfl
        omega
    exact aux i.val i rfl
  intro i j hji
  by_cases hi : i.val < r
  · let t : Fin r := ⟨i.val, hi⟩
    have heq : Fin.castLE hr t = i := Fin.ext rfl
    have hjp : j < p t := by
      have := hcol t
      change j.val < (p t).val
      change i.val ≤ (p t).val at this
      omega
    simpa only [heq] using (hpiv t).2 j hjp
  · exact hzero i (by omega) j

/-- W20: exact pivoted LU, including rank-deficient and empty matrices. -/
theorem exact_pivoted_lu : Specs.NumAnalysis206.PivotedLU.exact_pivoted_lu := by
  intro K _ n A
  obtain ⟨p, L, U, ps, ht⟩ := run_exists A 0 0 (by intro i j _ hj; omega)
  have hf := ht.factorization
  have he := ht.rowEchelon
  exact ⟨p, L, U, ps, ht, ⟨p, rfl⟩, hf.1, he, echelon_upperTriangular he,
    (permutationMatrix_mul p A).trans hf.2⟩

end NumAnalysis206.PivotedLU
