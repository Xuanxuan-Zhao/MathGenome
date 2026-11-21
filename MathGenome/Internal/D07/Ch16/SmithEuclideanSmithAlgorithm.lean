import MathGenome.Internal.Specs.D07.Ch16.SmithEuclideanSmithAlgorithm
import Mathlib.Data.Matrix.PEquiv
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Order.WellFounded

universe u

namespace D07.Ch16.SmithEuclideanSmithAlgorithm

open Specs.D07.Ch16.SmithEuclideanSmithAlgorithm
open Specs.D07.Ch10.EuclideanDefinition

variable {R : Type u} [CommRing R] {m n : ℕ}

@[simp] theorem execute_nil (A : Matrix (Fin m) (Fin n) R) : execute [] A = A := rfl

@[simp] theorem execute_cons (o : Operation R m n) (ops) (A : Matrix (Fin m) (Fin n) R) :
    execute (o :: ops) A = execute ops (o.apply A) := rfl

@[simp] theorem execute_append (ops₁ ops₂ : List (Operation R m n))
    (A : Matrix (Fin m) (Fin n) R) :
    execute (ops₁ ++ ops₂) A = execute ops₂ (execute ops₁ A) :=
  List.foldl_append

namespace Reachable

theorem refl (A : Matrix (Fin m) (Fin n) R) : Reachable A A := ⟨[], rfl⟩

theorem step (o : Operation R m n) (A : Matrix (Fin m) (Fin n) R) :
    Reachable A (o.apply A) := ⟨[o], rfl⟩

theorem trans {A B C : Matrix (Fin m) (Fin n) R}
    (h : Reachable A B) (k : Reachable B C) : Reachable A C := by
  obtain ⟨l, rfl⟩ := h
  obtain ⟨l', rfl⟩ := k
  exact ⟨l ++ l', execute_append l l' A⟩

end Reachable

/-- Each allowed operation is multiplication on exactly one side by a unit. -/
theorem operation_factors (o : Operation R m n) (A : Matrix (Fin m) (Fin n) R) :
    ∃ (P : Matrix (Fin m) (Fin m) R) (Q : Matrix (Fin n) (Fin n) R),
      IsUnit P ∧ IsUnit Q ∧ o.apply A = P * A * Q := by
  cases o with
  | swapRows i j =>
    let S : Matrix (Fin m) (Fin m) R := (Equiv.swap i j).toPEquiv.toMatrix
    have hS : S * S = 1 := by
      rw [PEquiv.toMatrix_toPEquiv_mul]
      ext k l
      simp [S, PEquiv.toMatrix_apply, Matrix.submatrix_apply, Matrix.one_apply]
    refine ⟨S, 1, IsUnit.of_mul_eq_one S hS, isUnit_one, ?_⟩
    rw [Matrix.mul_one, PEquiv.toMatrix_toPEquiv_mul]
    rfl
  | swapCols i j =>
    let S : Matrix (Fin n) (Fin n) R := (Equiv.swap i j).toPEquiv.toMatrix
    have hS : S * S = 1 := by
      rw [PEquiv.toMatrix_toPEquiv_mul]
      ext k l
      simp [S, PEquiv.toMatrix_apply, Matrix.submatrix_apply, Matrix.one_apply]
    refine ⟨1, S, isUnit_one, IsUnit.of_mul_eq_one S hS, ?_⟩
    rw [Matrix.one_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  | addRow i j h c =>
    let t : Matrix.TransvectionStruct (Fin m) R := ⟨i, j, h, c⟩
    refine ⟨t.toMatrix, 1, IsUnit.of_mul_eq_one t.inv.toMatrix t.mul_inv, isUnit_one, ?_⟩
    rw [Matrix.mul_one]
    ext k l
    by_cases hk : k = i
    · subst k
      simp [Operation.apply, t, Matrix.TransvectionStruct.toMatrix]
    · simp [Operation.apply, t, Matrix.TransvectionStruct.toMatrix, hk,
        Matrix.transvection_mul_apply_of_ne]
  | addCol i j h c =>
    let t : Matrix.TransvectionStruct (Fin n) R := ⟨j, i, h.symm, c⟩
    refine ⟨1, t.toMatrix, isUnit_one, IsUnit.of_mul_eq_one t.inv.toMatrix t.mul_inv, ?_⟩
    rw [Matrix.one_mul]
    ext k l
    by_cases hl : l = i
    · subst l
      simp [Operation.apply, t, Matrix.TransvectionStruct.toMatrix]
    · simp [Operation.apply, t, Matrix.TransvectionStruct.toMatrix, hl,
        Matrix.mul_transvection_apply_of_ne]

theorem operationCorrectness : OperationCorrectness.{u} := by
  intro R _ m n ops
  induction ops with
  | nil =>
    intro A
    exact ⟨1, 1, isUnit_one, isUnit_one, by simp⟩
  | cons o ops ih =>
    intro A
    obtain ⟨P, Q, hp, hq, h⟩ := operation_factors o A
    obtain ⟨P', Q', hp', hq', h'⟩ := ih (o.apply A)
    exact ⟨P' * P, Q * Q', hp'.mul hp, hq.mul hq', by
      rw [execute_cons, h', h]
      simp only [Matrix.mul_assoc]⟩

/-- Any common entry divisor is preserved by every elementary operation. -/
theorem operation_preserves_divisor (o : Operation R m n)
    (A : Matrix (Fin m) (Fin n) R) (a : R) (h : ∀ i j, a ∣ A i j) :
    ∀ i j, a ∣ o.apply A i j := by
  cases o with
  | swapRows x y => exact fun i j => h _ _
  | swapCols x y => exact fun i j => h _ _
  | addRow x y hxy c =>
    intro i j
    dsimp [Operation.apply]
    split_ifs
    · exact dvd_add (h i j) (dvd_mul_of_dvd_right (h y j) c)
    · exact h i j
  | addCol x y hxy c =>
    intro i j
    dsimp [Operation.apply]
    split_ifs
    · exact dvd_add (h i j) (dvd_mul_of_dvd_right (h i y) c)
    · exact h i j

theorem reachable_preserves_divisor {A B : Matrix (Fin m) (Fin n) R}
    (h : Reachable A B) (a : R) (ha : ∀ i j, a ∣ A i j) : ∀ i j, a ∣ B i j := by
  obtain ⟨ops, rfl⟩ := h
  induction ops generalizing A with
  | nil => exact ha
  | cons o ops ih => exact ih (operation_preserves_divisor o A a ha)

/-- Nondivisibility forces a nonzero remainder for any upstream division data,
even though those data do not require unique remainders. -/
theorem remainder_nonzero [IsDomain R] (d : EuclideanData R) {a b : R}
    (ha : a ≠ 0) (h : ¬ a ∣ b) : d.remainder b a ≠ 0 := by
  intro hr
  apply h
  refine ⟨d.quotient b a, ?_⟩
  simpa [hr, mul_comm] using d.division b a ha

theorem blockFailureReduction : BlockFailureReduction.{u} := by
  intro R _ _ d m n A ha hc hr i j hij
  have hi : i ≠ 0 := by
    rintro rfl
    apply hij
    by_cases h : j = 0
    · subst j; exact dvd_refl _
    · rw [hr j h]; exact dvd_zero _
  have hj : j ≠ 0 := by
    rintro rfl
    apply hij
    rw [hc i hi]
    exact dvd_zero _
  let q := d.quotient (A i j) (A 0 0)
  let ops : List (Operation R (m+1) (n+1)) :=
    [.addRow 0 i hi.symm 1, .addCol j 0 hj (-q), .swapCols 0 j]
  have hval : execute ops A 0 0 = d.remainder (A i j) (A 0 0) := by
    dsimp only [ops]
    rw [execute_cons, execute_cons, execute_cons, execute_nil]
    simp only [Operation.apply, Matrix.of_apply, Equiv.swap_apply_left]
    rw [hr j hj, hc i hi]
    simp only [zero_add, one_mul, add_zero]
    have hd := d.division (A i j) (A 0 0) ha
    dsimp [q]
    rw [neg_mul, ← sub_eq_add_neg]
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hd)
  refine ⟨ops, hval, ?_, ?_⟩
  · rw [hval]
    exact remainder_nonzero d ha hij
  · rw [hval]
    exact (d.decrease (A i j) (A 0 0) ha).resolve_left (remainder_nonzero d ha hij)

theorem noInfiniteRestarts : NoInfiniteRestarts.{u} := by
  intro R _ _ d p h
  exact (wellFounded_iff_isEmpty_descending_chain.mp d.wellFounded).false ⟨p, h⟩


/-- Transposition exchanges row and column instructions. -/
def transposeOperation : Operation R m n → Operation R n m
  | .swapRows i j => .swapCols i j
  | .swapCols i j => .swapRows i j
  | .addRow i j h c => .addCol i j h c
  | .addCol i j h c => .addRow i j h c

@[simp] theorem transposeOperation_apply (o : Operation R m n)
    (A : Matrix (Fin m) (Fin n) R) :
    (transposeOperation o).apply A.transpose = (o.apply A).transpose := by
  cases o <;> rfl

theorem execute_transpose (ops : List (Operation R m n))
    (A : Matrix (Fin m) (Fin n) R) :
    execute (ops.map transposeOperation) A.transpose = (execute ops A).transpose := by
  induction ops generalizing A with
  | nil => rfl
  | cons o ops ih =>
    rw [List.map_cons, execute_cons, transposeOperation_apply, ih, execute_cons]

theorem Reachable.transpose {A B : Matrix (Fin m) (Fin n) R}
    (h : Reachable A B) : Reachable A.transpose B.transpose := by
  obtain ⟨ops, rfl⟩ := h
  exact ⟨ops.map transposeOperation, execute_transpose ops A⟩

/-- Finitely many row subtractions clear a divisible column while leaving the
pivot row unchanged. The invariant states exactly what happens to every
entry in that column, including rows not yet processed. -/
theorem clear_column_subset (A : Matrix (Fin m) (Fin n) R)
    (p : Fin m) (c : Fin n) (hdiv : ∀ i, A p c ∣ A i c)
    (s : Finset (Fin m)) (hp : p ∉ s) :
    ∃ B, Reachable A B ∧ (∀ j, B p j = A p j) ∧
      (∀ i, B i c = if i ∈ s then 0 else A i c) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨A, Reachable.refl A, fun _ => rfl, by simp⟩
  | @insert i s his ih =>
    have hip : i ≠ p := by intro he; subst i; exact hp (Finset.mem_insert_self _ _)
    obtain ⟨B, hB, hrow, hcol⟩ := ih (fun h => hp (Finset.mem_insert_of_mem h))
    obtain ⟨q, hq⟩ := hdiv i
    let o : Operation R m n := .addRow i p hip (-q)
    refine ⟨o.apply B, Reachable.trans hB (Reachable.step o B), ?_, ?_⟩
    · intro j
      simpa [o, Operation.apply, hip.symm] using hrow j
    · intro k
      by_cases hk : k = i
      · subst k
        simp only [o, Operation.apply, Matrix.of_apply]
        rw [hcol, ite_eq_right his, hrow, hq]
        simp [mul_comm]
      · simp only [o, Operation.apply, Matrix.of_apply, ite_eq_right hk]
        rw [hcol]
        simp [Finset.mem_insert, hk]

theorem clear_column (A : Matrix (Fin m) (Fin n) R)
    (p : Fin m) (c : Fin n) (hdiv : ∀ i, A p c ∣ A i c) :
    ∃ B, Reachable A B ∧ (∀ j, B p j = A p j) ∧
      (∀ i, i ≠ p → B i c = 0) := by
  obtain ⟨B, hB, hr, hc⟩ := clear_column_subset A p c hdiv
    (Finset.univ.erase p) (Finset.notMem_erase p _)
  exact ⟨B, hB, hr, fun i hi => by simpa [hi] using hc i⟩

/-- The analogous finite column subtractions, obtained by transposing the
already proved row procedure. -/
theorem clear_row (A : Matrix (Fin m) (Fin n) R)
    (p : Fin m) (c : Fin n) (hdiv : ∀ j, A p c ∣ A p j) :
    ∃ B, Reachable A B ∧ (∀ i, B i c = A i c) ∧
      (∀ j, j ≠ c → B p j = 0) := by
  obtain ⟨B, hB, hr, hc⟩ := clear_column A.transpose c p hdiv
  exact ⟨B.transpose, Reachable.transpose hB, hr, hc⟩

/-- A first-column entry not divisible by a nonzero pivot gives a strict
pivot replacement in two elementary instructions. -/
theorem reduce_column_entry [IsDomain R] (d : EuclideanData R)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) R)
    (ha : A 0 0 ≠ 0) (i : Fin (m+1)) (hi : ¬ A 0 0 ∣ A i 0) :
    ∃ B, Reachable A B ∧ B 0 0 ≠ 0 ∧ d.smaller (B 0 0) (A 0 0) := by
  have hi0 : i ≠ 0 := by rintro rfl; exact hi (dvd_refl _)
  let q := d.quotient (A i 0) (A 0 0)
  let ops : List (Operation R (m+1) (n+1)) :=
    [.addRow i 0 hi0 (-q), .swapRows 0 i]
  have hv : execute ops A 0 0 = d.remainder (A i 0) (A 0 0) := by
    dsimp only [ops]
    rw [execute_cons, execute_cons, execute_nil]
    simp only [Operation.apply, Matrix.of_apply, Equiv.swap_apply_left]
    rw [neg_mul, ← sub_eq_add_neg]
    exact sub_eq_iff_eq_add.mpr (by simpa [q, add_comm] using d.division (A i 0) (A 0 0) ha)
  refine ⟨execute ops A, ⟨ops, rfl⟩, ?_, ?_⟩
  · rw [hv]; exact remainder_nonzero d ha hi
  · rw [hv]
    exact (d.decrease _ _ ha).resolve_left (remainder_nonzero d ha hi)

/-- Pivot preparation terminates by well-founded induction on the current
nonzero pivot, including the restart caused by the remaining block. Between
recursive calls only finite clearing traces are used. -/
theorem prepare_pivot [IsDomain R] (d : EuclideanData R)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) R) (ha : A 0 0 ≠ 0) :
    ∃ B, PivotRun d A B ∧ Reachable A B ∧ B 0 0 ≠ 0 ∧
      (∀ i, i ≠ 0 → B i 0 = 0) ∧ (∀ j, j ≠ 0 → B 0 j = 0) ∧
      (∀ i j, B 0 0 ∣ B i j) := by
  classical
  generalize he : A 0 0 = a at *
  induction a using d.wellFounded.induction generalizing A with
  | h a ih =>
    have ha' : A 0 0 ≠ 0 := by rwa [he]
    by_cases hcol : ∀ i, A 0 0 ∣ A i 0
    · obtain ⟨B, hB, hrB, hcB⟩ := clear_column A 0 0 hcol
      have hb : B 0 0 ≠ 0 := by rwa [hrB]
      by_cases hrow : ∀ j, B 0 0 ∣ B 0 j
      · obtain ⟨C, hC, hcC, hrC⟩ := clear_row B 0 0 hrow
        have hc : C 0 0 ≠ 0 := by rwa [hcC]
        have hcolC : ∀ i, i ≠ 0 → C i 0 = 0 := by
          intro i hi; rw [hcC]; exact hcB i hi
        by_cases hblock : ∀ i j, C 0 0 ∣ C i j
        · refine ⟨C, ?_, Reachable.trans hB hC, hc, hcolC, hrC, hblock⟩
          exact .finish (Reachable.trans hB hC) (by rw [hcC, hrB]) ha' hcolC hrC hblock
        · obtain ⟨i, j, hij⟩ := not_forall.mp hblock |>.imp fun i hi => by
            exact not_forall.mp hi
          obtain ⟨ops, hv, hn, hlt⟩ := blockFailureReduction R d m n C hc hcolC hrC i j hij
          have hlt' : d.smaller (execute ops C 0 0) a := by
            simpa only [hcC, hrB, he] using hlt
          obtain ⟨D, hrun, hD, hd⟩ := ih (execute ops C 0 0) hlt' (execute ops C) rfl hn
          have hprefix : Reachable A (execute ops C) :=
            Reachable.trans (Reachable.trans hB hC) ⟨ops, rfl⟩
          exact ⟨D, .restart hprefix hn (by simpa only [he] using hlt') hrun,
            Reachable.trans hprefix hD, hd⟩
      · obtain ⟨j, hj⟩ := not_forall.mp hrow
        obtain ⟨C, hC, hc, hlt⟩ := reduce_column_entry d B.transpose hb j hj
        have hlt' : d.smaller (C.transpose 0 0) a := by
          simpa only [Matrix.transpose_apply, hrB, he] using hlt
        obtain ⟨D, hrun, hD, hd⟩ := ih (C.transpose 0 0) hlt' C.transpose rfl hc
        have hprefix : Reachable A C.transpose := Reachable.trans hB (Reachable.transpose hC)
        exact ⟨D, .restart hprefix hc (by simpa only [he] using hlt') hrun,
          Reachable.trans hprefix hD, hd⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hcol
      obtain ⟨B, hB, hb, hlt⟩ := reduce_column_entry d A ha' i hi
      have hlt' : d.smaller (B 0 0) a := by simpa only [he] using hlt
      obtain ⟨C, hrun, hC, hc⟩ := ih (B 0 0) hlt' B rfl hb
      exact ⟨C, .restart hB hb hlt hrun, Reachable.trans hB hC, hc⟩


theorem pivotPreparationTerminates : PivotPreparationTerminates.{u} := by
  intro R _ _ d m n A ha
  obtain ⟨B, hrun, _⟩ := prepare_pivot d A ha
  exact ⟨B, hrun⟩

theorem pivotRunCorrectness : PivotRunCorrectness.{u} := by
  intro R _ _ d m n A B h
  induction h with
  | finish trace pivot nonzero column row divides =>
    exact ⟨trace, pivot ▸ nonzero, column, row, divides⟩
  | restart trace nonzero decrease tail ih =>
    exact ⟨Reachable.trans trace ih.1, ih.2⟩

/-- Adjoin a pivot and zero border to a smaller rectangular matrix. -/
def border (a : R) (T : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin (m+1)) (Fin (n+1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases a (fun _ => 0) j)
    (fun i => Fin.cases 0 (fun j => T i j) j) i

@[simp] theorem border_zero_zero (a : R) (T : Matrix (Fin m) (Fin n) R) :
    border a T 0 0 = a := rfl
@[simp] theorem border_zero_succ (a : R) (T : Matrix (Fin m) (Fin n) R) (j : Fin n) :
    border a T 0 j.succ = 0 := rfl
@[simp] theorem border_succ_zero (a : R) (T : Matrix (Fin m) (Fin n) R) (i : Fin m) :
    border a T i.succ 0 = 0 := rfl
@[simp] theorem border_succ_succ (a : R) (T : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    border a T i.succ j.succ = T i j := rfl

/-- Operate only on rows and columns belonging to the smaller block. -/
def liftOperation : Operation R m n → Operation R (m+1) (n+1)
  | .swapRows i j => .swapRows i.succ j.succ
  | .swapCols i j => .swapCols i.succ j.succ
  | .addRow i j h c => .addRow i.succ j.succ (by simpa using h) c
  | .addCol i j h c => .addCol i.succ j.succ (by simpa using h) c

@[simp] theorem swap_succ (i j k : Fin m) :
    Equiv.swap i.succ j.succ k.succ = (Equiv.swap i j k).succ := by
  simp only [Equiv.swap_apply_def, Fin.succ_inj]
  split_ifs <;> rfl

@[simp] theorem swap_succ_zero (i j : Fin m) :
    Equiv.swap i.succ j.succ (0 : Fin (m+1)) = 0 := by
  simp [Equiv.swap_apply_def, Fin.ext_iff]

@[simp] theorem liftOperation_apply_border (o : Operation R m n)
    (a : R) (T : Matrix (Fin m) (Fin n) R) :
    (liftOperation o).apply (border a T) = border a (o.apply T) := by
  cases o <;> ext i j <;>
    refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [liftOperation, Operation.apply, Fin.ext_iff]

/-- All subsequent block operations leave the finished pivot and its zero
border in place. -/
theorem execute_lift_border (ops : List (Operation R m n)) (a : R)
    (T : Matrix (Fin m) (Fin n) R) :
    execute (ops.map liftOperation) (border a T) = border a (execute ops T) := by
  induction ops generalizing T with
  | nil => rfl
  | cons o ops ih =>
    rw [List.map_cons, execute_cons, liftOperation_apply_border, ih, execute_cons]

theorem Reachable.border {T U : Matrix (Fin m) (Fin n) R}
    (h : Reachable T U) (a : R) : Reachable (border a T) (border a U) := by
  obtain ⟨ops, rfl⟩ := h
  exact ⟨ops.map liftOperation, execute_lift_border ops a T⟩

/-- A matrix with a cleared first row and column is exactly its bordered
remaining block. -/
theorem eq_border (A : Matrix (Fin (m+1)) (Fin (n+1)) R)
    (hc : ∀ i, i ≠ 0 → A i 0 = 0) (hr : ∀ j, j ≠ 0 → A 0 j = 0) :
    A = border (A 0 0) (A.submatrix Fin.succ Fin.succ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · simpa using hr j.succ (Fin.succ_ne_zero j)
  · simpa using hc i.succ (Fin.succ_ne_zero i)
  · rfl

theorem smith_zero : SmithForm (0 : Matrix (Fin m) (Fin n) R) := by
  refine ⟨0, Nat.zero_le _, Nat.zero_le _, Fin.elim0, ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i j; simp

/-- Adding a pivot dividing the whole remaining block joins the two chains.
This uses preservation of entry divisibility, rather than assuming the
smaller block's final diagonal entries retain a particular representative. -/
theorem border_smith {a : R} {T : Matrix (Fin m) (Fin n) R}
    (ha : a ≠ 0) (hT : SmithForm T) (hdiv : ∀ i j, a ∣ T i j) :
    SmithForm (border a T) := by
  obtain ⟨s, hm, hn, t, ht, hchain, hentries⟩ := hT
  have hdt : ∀ i, a ∣ t i := by
    intro i
    have h := hdiv (Fin.castLE hm i) (Fin.castLE hn i)
    simpa [hentries, i.isLt] using h
  refine ⟨s+1, Nat.succ_le_succ hm, Nat.succ_le_succ hn,
    Fin.cases a t, ?_, ?_, ?_⟩
  · intro i
    exact Fin.cases ha ht i
  · intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i
    · intro _
      exact Fin.cases (dvd_refl a) hdt j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h; exact (Nat.not_succ_le_zero i.val h).elim
      · intro h; exact hchain i j (Nat.le_of_succ_le_succ h)
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
    · simp
    · simp only [border_succ_succ, Fin.val_succ, Nat.add_right_cancel_iff,
        Nat.add_lt_add_iff_right]
      split_ifs with h
      · change T i j = t ⟨i.val, h.2⟩
        simpa only [dite_eq_left h] using hentries i j
      · simpa only [dite_eq_right h] using hentries i j

/-- Move any given nonzero entry into the pivot position, without changing
matrix dimensions. -/
theorem initial_pivot (A : Matrix (Fin (m+1)) (Fin (n+1)) R)
    (hA : A ≠ 0) : ∃ B, Reachable A B ∧ B 0 0 ≠ 0 := by
  classical
  have hex : ∃ i j, A i j ≠ 0 := by
    by_contra h
    apply hA
    ext i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hex
  let ops : List (Operation R (m+1) (n+1)) := [.swapRows 0 i, .swapCols 0 j]
  refine ⟨execute ops A, ⟨ops, rfl⟩, ?_⟩
  dsimp only [ops]
  rw [execute_cons, execute_cons, execute_nil]
  simpa [Operation.apply] using hij

/-- The dimension induction is separate from pivot descent. It handles
empty rectangular matrices and a zero block by the empty trace. -/
theorem smith_reachable [IsDomain R] (d : EuclideanData R)
    (A : Matrix (Fin m) (Fin n) R) : ∃ B, Reachable A B ∧ SmithForm B := by
  classical
  induction m generalizing n with
  | zero =>
    have hA : A = 0 := by ext i; exact Fin.elim0 i
    exact ⟨0, ⟨[], by simpa only [execute_nil] using hA⟩, smith_zero⟩
  | succ m ih =>
    cases n with
    | zero =>
      have hA : A = 0 := by ext i j; exact Fin.elim0 j
      exact ⟨0, ⟨[], by simpa only [execute_nil] using hA⟩, smith_zero⟩
    | succ n =>
      by_cases hA : A = 0
      · exact ⟨0, ⟨[], by simpa only [execute_nil] using hA⟩, smith_zero⟩
      obtain ⟨B, hB, hb⟩ := initial_pivot A hA
      obtain ⟨C, _, hC, hc, hcol, hrow, hdiv⟩ := prepare_pivot d B hb
      let T := C.submatrix Fin.succ Fin.succ
      obtain ⟨U, hU, hu⟩ := ih T
      have hdivT : ∀ i j, C 0 0 ∣ T i j := fun i j => hdiv i.succ j.succ
      have hdivU := reachable_preserves_divisor hU (C 0 0) hdivT
      refine ⟨border (C 0 0) U, Reachable.trans hB (Reachable.trans hC ?_),
        border_smith hc hu hdivU⟩
      rw [eq_border C hcol hrow]
      exact Reachable.border hU (C 0 0)

theorem algorithmTerminates : AlgorithmTerminates.{u} := by
  intro R _ _ d m n A
  obtain ⟨B, ⟨ops, rfl⟩, hB⟩ := smith_reachable d A
  exact ⟨ops, hB⟩

theorem smithConstruction : SmithConstruction.{u} := by
  intro R _ _ d m n A
  obtain ⟨ops, hs⟩ := algorithmTerminates R d m n A
  obtain ⟨P, Q, hp, hq, he⟩ := operationCorrectness R m n ops A
  exact ⟨ops, P, Q, hp, hq, he, he ▸ hs⟩

end D07.Ch16.SmithEuclideanSmithAlgorithm
