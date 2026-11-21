import MathGenome.Internal.Specs.D05.M01.Elimination.Forward
import MathGenome.Internal.D05.M01.RowOps
import MathGenome.Internal.D05.M01.Echelon

namespace D05.M01.Elimination

open RowOps
universe u
variable {K : Type u} [Field K] {m n : ℕ}

@[simp] theorem applyOps_nil (A : Matrix (Fin m) (Fin n) K) : applyOps [] A = A := rfl

@[simp] theorem applyOps_append (l₁ l₂ : List (RowOperation K m))
    (A : Matrix (Fin m) (Fin n) K) :
    applyOps (l₁ ++ l₂) A = applyOps l₂ (applyOps l₁ A) := by
  exact List.foldl_append

@[simp] theorem applyOps_singleton (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) : applyOps [op] A = applyOp op A := rfl

/-- Finitely many additions to distinct rows can be implemented by a list
of permitted operations; all coefficients refer to the original pivot row. -/
theorem simultaneous_add (A : Matrix (Fin m) (Fin n) K) (r : Fin m)
    (S : Finset (Fin m)) (a : Fin m → K) (hr : r ∉ S) :
    ∃ ops, applyOps ops A =
      fun i j => if i ∈ S then A i j + a i * A r j else A i j := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨[], by ext i j; simp⟩
  | @insert t S ht ih =>
    have hrt : r ≠ t := by intro h; apply hr; simp [h]
    have hrs : r ∉ S := by intro h; apply hr; simp [h]
    obtain ⟨ops, hops⟩ := ih hrs
    refine ⟨ops ++ [.add t r (a t) hrt.symm], ?_⟩
    rw [applyOps_append, applyOps_singleton, hops]
    ext i j
    by_cases hi : i = t
    · subst i
      simp [applyOp, ht, hrs]
    · simp [applyOp, hi]

/-- The explicit swap/normalize/clear formula is a finite sequence of the
three permitted operations. The only scale used is the inverse of a proved
nonzero original pivot. -/
theorem pivotMatrix_reachable (A : Matrix (Fin m) (Fin n) K)
    (r q : Fin m) (d : Fin n) (h : A q d ≠ 0) :
    ∃ ops, applyOps ops A = pivotMatrix A r q d := by
  classical
  let S : Matrix (Fin m) (Fin n) K := fun i j => A (Equiv.swap r q i) j
  have hS : ∃ ops, applyOps ops A = S := by
    by_cases hrq : r = q
    · subst q
      exact ⟨[], by simp [S]⟩
    · exact ⟨[.swap r q hrq], rfl⟩
  obtain ⟨ops₁, h₁⟩ := hS
  let N := applyOp (.scale r (A q d)⁻¹ (inv_ne_zero h)) S
  obtain ⟨ops₂, h₂⟩ := simultaneous_add N r (Finset.univ.filter (r < ·))
    (fun i => -N i d) (by simp)
  refine ⟨ops₁ ++ [.scale r (A q d)⁻¹ (inv_ne_zero h)] ++ ops₂, ?_⟩
  rw [applyOps_append, applyOps_append, h₁, applyOps_singleton]
  change applyOps ops₂ N = _
  rw [h₂]
  ext i j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_mul,
    ← sub_eq_add_neg]
  rfl


private theorem pivotMatrix_properties (A : Matrix (Fin m) (Fin n) K)
    (r q : Fin m) (d : Fin n) (hrq : r ≤ q) (hp : A q d ≠ 0)
    (hz : ∀ i j, r ≤ i → j < d → A i j = 0) :
    (∀ i, i < r → pivotMatrix A r q d i = A i) ∧
    (∀ i j, j < d → pivotMatrix A r q d i j = A i j) ∧
    (pivotMatrix A r q d).IsLeadingEntry r d ∧
    pivotMatrix A r q d r d = 1 ∧
    LowerZero (pivotMatrix A r q d) (r.val + 1) (d.val + 1) := by
  classical
  have above : ∀ i, i < r → pivotMatrix A r q d i = A i := by
    intro i hir
    have hiq : i ≠ q := ne_of_lt (lt_of_lt_of_le hir hrq)
    funext j
    simp [pivotMatrix, not_lt_of_ge (le_of_lt hir), ne_of_lt hir,
      Equiv.swap_apply_of_ne_of_ne (ne_of_lt hir) hiq]
  have swzero : ∀ i j, r ≤ i → j < d → A (Equiv.swap r q i) j = 0 := by
    intro i j hri hj
    by_cases hir : i = r
    · subst i
      simpa using hz q j hrq hj
    by_cases hiq : i = q
    · subst i
      simpa using hz r j le_rfl hj
    · simpa [Equiv.swap_apply_of_ne_of_ne hir hiq] using hz i j hri hj
  have lower_left : ∀ i j, r ≤ i → j < d → pivotMatrix A r q d i j = 0 := by
    intro i j hri hj
    have z₁ := swzero i j hri hj
    have z₂ := hz q j hrq hj
    simp [pivotMatrix, z₁, z₂]
  have pivot : pivotMatrix A r q d r d = 1 := by
    simp [pivotMatrix, hp]
  refine ⟨above, ?_, ⟨?_, ?_⟩, pivot, ?_⟩
  · intro i j hj
    by_cases hir : i < r
    · exact congrFun (above i hir) j
    · rw [lower_left i j (le_of_not_gt hir) hj, hz i j (le_of_not_gt hir) hj]
  · intro j hj
    exact lower_left r j le_rfl hj
  · rw [pivot]
    exact one_ne_zero
  · intro i j hri hj
    have hri' : r < i := by exact hri
    have hir : i ≠ r := ne_of_gt hri'
    have hdi : j ≤ d := by exact Nat.lt_succ_iff.mp hj
    rcases hdi.eq_or_lt with h | h
    · subst j
      simp [pivotMatrix, hri', hir, hp]
    · exact lower_left i j (le_of_lt hri') h

namespace Forward

/-- Every nonempty remaining part has a leftmost column and a nonzero pivot
which can safely be inverted. -/
theorem pivot_stage_exists (A : Matrix (Fin m) (Fin n) K)
    (r : Fin m) (c : ℕ) (hz : LowerZero A r.val c)
    (hne : ∃ i j, r ≤ i ∧ A i j ≠ 0) :
    ∃ d B, PivotStage A B r c d := by
  classical
  have hex : ∃ d : Fin n, d ∈ {d | ∃ i, r ≤ i ∧ A i d ≠ 0} := by
    obtain ⟨i, j, hi, hij⟩ := hne
    exact ⟨j, i, hi, hij⟩
  obtain ⟨d, ⟨q, hrq, hp⟩, hmin⟩ := wellFounded_lt.has_min
    {d : Fin n | ∃ i, r ≤ i ∧ A i d ≠ 0} hex
  have hd : c ≤ d.val := by
    by_contra h
    exact hp (hz q d hrq (Nat.lt_of_not_ge h))
  have hleft : ∀ i j, r ≤ i → j < d → A i j = 0 := by
    intro i j hri hj
    by_contra hij
    exact hmin j ⟨i, hri, hij⟩ hj
  exact ⟨d, pivotMatrix A r q d, hd, q, hrq, hp, hleft, rfl,
    pivotMatrix_reachable A r q d hp⟩

theorem pivot_stage_invariants (A B : Matrix (Fin m) (Fin n) K)
    (r : Fin m) (c : ℕ) (d : Fin n) (hs : PivotStage A B r c d) :
    (∀ i, i < r → B i = A i) ∧
    (∀ i j, j.val < c → B i j = A i j) ∧
    B.IsLeadingEntry r d ∧ B r d = 1 ∧ LowerZero B (r.val + 1) (d.val + 1) := by
  obtain ⟨hd, q, hrq, hp, hz, rfl, _⟩ := hs
  obtain ⟨ha, hl, hp', h1, hlow⟩ := pivotMatrix_properties A r q d hrq hp hz
  exact ⟨ha, fun i j hj => hl i j (show j.val < d.val from lt_of_lt_of_le hj hd), hp', h1, hlow⟩


/-- Strong induction on the number of unused rows constructs a complete run. -/
theorem trace_exists (A : Matrix (Fin m) (Fin n) K) (r c : ℕ)
    (hz : LowerZero A r c) : ∃ ps B, ForwardTrace r c A ps B := by
  classical
  have main : ∀ k : ℕ, ∀ (r c : ℕ) (A : Matrix (Fin m) (Fin n) K),
      m - r ≤ k → LowerZero A r c → ∃ ps B, ForwardTrace r c A ps B := by
    intro k
    induction k with
    | zero =>
      intro r c A hk _
      refine ⟨[], A, .stop ?_⟩
      intro i hi
      have := i.isLt
      omega
    | succ k ih =>
      intro r c A hk hz
      by_cases hzero : ∀ i : Fin m, r ≤ i.val → A i = 0
      · exact ⟨[], A, .stop hzero⟩
      · have hex : ∃ i j, r ≤ i.val ∧ A i j ≠ 0 := by
          push Not at hzero
          obtain ⟨i, hri, hi⟩ := hzero
          obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
          exact ⟨i, j, hri, hj⟩
        obtain ⟨i, j, hri, hij⟩ := hex
        have hr : r < m := lt_of_le_of_lt hri i.isLt
        let row : Fin m := ⟨r, hr⟩
        obtain ⟨d, B, hs⟩ := pivot_stage_exists A row c hz ⟨i, j, hri, hij⟩
        have hzB := (pivot_stage_invariants A B row c d hs).2.2.2.2
        obtain ⟨ps, C, ht⟩ := ih (r + 1) (d.val + 1) B (by omega) hzB
        exact ⟨d :: ps, C, .step hr hs ht⟩
  exact main (m - r) r c A le_rfl hz

/-- Every trace concatenates to an ordinary finite row-operation sequence. -/
theorem trace_reachable {A B : Matrix (Fin m) (Fin n) K} {r c : ℕ}
    {ps : List (Fin n)} (ht : ForwardTrace r c A ps B) :
    ∃ ops, applyOps ops A = B := by
  induction ht with
  | stop => exact ⟨[], rfl⟩
  | step hr hs ht ih =>
    obtain ⟨_, _, _, _, _, _, ops₁, h₁⟩ := hs
    obtain ⟨ops₂, h₂⟩ := ih
    exact ⟨ops₁ ++ ops₂, by rw [applyOps_append, h₁, h₂]⟩

/-- In particular, each completed stage increases the row cursor by one;
its column cursor goes strictly past the preceding pivot. -/
theorem trace_bounds {A B : Matrix (Fin m) (Fin n) K} {r c : ℕ}
    {ps : List (Fin n)} (ht : ForwardTrace r c A ps B)
    (hr : r ≤ m) (hc : c ≤ n) :
    ps.length ≤ min (m - r) (n - c) ∧ ps.Pairwise (· < ·) ∧
      ∀ d ∈ ps, c ≤ d.val := by
  induction ht with
  | stop => simp
  | @step r c A B C d ps hrow hs ht ih =>
    have hd := hs.1
    obtain ⟨hlen, hpair, hall⟩ := ih (by omega) (by have := d.isLt; omega)
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_cons]
      apply le_min
      · have := le_trans hlen (min_le_left _ _)
        omega
      · have := le_trans hlen (min_le_right _ _)
        omega
    · rw [List.pairwise_cons]
      exact ⟨fun e he => (show d.val < e.val from hall e he), hpair⟩
    · intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e; exact hd
      · have := hall e he
        omega

/-- All previously completed rows and columns survive every later stage. -/
theorem trace_preserves {A B : Matrix (Fin m) (Fin n) K} {r c : ℕ}
    {ps : List (Fin n)} (ht : ForwardTrace r c A ps B) :
    (∀ i : Fin m, i.val < r → B i = A i) ∧
      (∀ i j, j.val < c → B i j = A i j) := by
  induction ht with
  | stop => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  | @step r c A B C d ps hr hs ht ih =>
    obtain ⟨ha, hl, _, _, _⟩ := pivot_stage_invariants A B ⟨r, hr⟩ c d hs
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (ih.1 i (by omega)).trans (ha i hi)
    · intro i j hj
      exact (ih.2 i j (by have := hs.1; omega)).trans (hl i j hj)

/-- The pivot list records the actual leading entries of the final matrix.
The first unused row is exactly r + ps.length. -/
theorem trace_pivots {A B : Matrix (Fin m) (Fin n) K} {r c : ℕ}
    {ps : List (Fin n)} (ht : ForwardTrace r c A ps B) :
    (∀ t : Fin ps.length, ∃ i : Fin m, i.val = r + t.val ∧
      B.IsLeadingEntry i (ps.get t) ∧ B i (ps.get t) = 1) ∧
    (∀ i : Fin m, r + ps.length ≤ i.val → B i = 0) := by
  induction ht with
  | stop hz => exact ⟨fun t => Fin.elim0 t, by simpa using hz⟩
  | @step r c A B C d ps hr hs ht ih =>
    obtain ⟨ha, _⟩ := trace_preserves ht
    obtain ⟨_, _, hp, h1, _⟩ := pivot_stage_invariants A B ⟨r, hr⟩ c d hs
    refine ⟨?_, ?_⟩
    · intro t
      refine Fin.cases ?_ (fun t => ?_) t
      · refine ⟨⟨r, hr⟩, by simp, ?_, ?_⟩
        · change C.IsLeadingEntry ⟨r, hr⟩ d
          change (∀ j < d, C ⟨r, hr⟩ j = 0) ∧ C ⟨r, hr⟩ d ≠ 0
          rw [ha ⟨r, hr⟩ (by simp)]
          exact hp
        · change C ⟨r, hr⟩ d = 1
          rw [ha ⟨r, hr⟩ (by simp)]
          exact h1
      · obtain ⟨i, hi, hpi, h1i⟩ := ih.1 t
        exact ⟨i, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi,
          hpi, h1i⟩
    · intro i hi
      apply ih.2 i
      simp only [List.length_cons] at hi
      omega

/-- The output is echelon on the processed suffix; with r=0 this is the
canonical Mathlib row-echelon predicate on the entire matrix. -/
theorem trace_echelon {A B : Matrix (Fin m) (Fin n) K} {r c : ℕ}
    {ps : List (Fin n)} (ht : ForwardTrace r c A ps B) :
    ∀ i k : Fin m, r ≤ i.val → i < k →
      ∀ j : Fin n, (∀ l < j, B i l = 0) → B k j = 0 := by
  induction ht with
  | stop hz =>
    intro i k hri hik j _
    exact congrFun (hz k (by exact le_trans hri (le_of_lt hik))) j
  | @step r c A B C d ps hr hs ht ih =>
    intro i k hri hik j hj
    by_cases hir : i.val = r
    · have hieq : i = (⟨r, hr⟩ : Fin m) := Fin.ext hir
      subst i
      obtain ⟨_, _, hp, _, hz⟩ := pivot_stage_invariants A B ⟨r, hr⟩ c d hs
      obtain ⟨ha, hl⟩ := trace_preserves ht
      have hpC : C ⟨r, hr⟩ d ≠ 0 := by
        rw [ha ⟨r, hr⟩ (by simp)]
        exact hp.2
      have hjd : j ≤ d := le_of_not_gt (fun hdj => hpC (hj d hdj))
      rw [hl k j (by exact Nat.lt_succ_of_le hjd)]
      exact hz k j (by exact hik) (by exact Nat.lt_succ_of_le hjd)
    · exact ih i k (by omega) hik j hj

/-- Gaussian forward elimination, including zero matrices and empty shapes. -/
theorem forward_elimination (A : Matrix (Fin m) (Fin n) K) :
    ∃ (ops : List (RowOperation K m)) (B : Matrix (Fin m) (Fin n) K)
      (ps : List (Fin n)), applyOps ops A = B ∧ ForwardTrace 0 0 A ps B ∧
      ps.length ≤ min m n ∧ ps.Pairwise (· < ·) ∧ B.IsRowEchelon := by
  obtain ⟨ps, B, ht⟩ := trace_exists A 0 0 (by intro i j _ hj; omega)
  obtain ⟨ops, hops⟩ := trace_reachable ht
  obtain ⟨hlen, hpair, _⟩ := trace_bounds ht (Nat.zero_le _) (Nat.zero_le _)
  refine ⟨ops, B, ps, hops, ht, ?_, hpair, ?_⟩
  · simpa using hlen
  · intro i k hik j hj
    exact trace_echelon ht i k (Nat.zero_le _) hik j hj

theorem zero_trace :
    ForwardTrace 0 0 (0 : Matrix (Fin m) (Fin n) K) [] 0 ∧
      applyOps ([] : List (RowOperation K m))
        (0 : Matrix (Fin m) (Fin n) K) = 0 ∧
      (0 : Matrix (Fin m) (Fin n) K).IsRowEchelon := by
  exact ⟨.stop (fun _ _ => rfl), rfl, fun _ _ _ _ _ => rfl⟩

theorem empty_rows (A : Matrix (Fin 0) (Fin n) K) :
    ForwardTrace 0 0 A [] A ∧ A.IsRowEchelon := by
  exact ⟨.stop (fun i => Fin.elim0 i), fun {i} => Fin.elim0 i⟩

theorem empty_columns (A : Matrix (Fin m) (Fin 0) K) :
    ForwardTrace 0 0 A [] A ∧ A.IsRowEchelon := by
  refine ⟨.stop (fun _ _ => Subsingleton.elim _ _), ?_⟩
  intro i k hik j
  exact Fin.elim0 j

end Forward
end D05.M01.Elimination
