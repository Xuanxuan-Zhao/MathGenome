import MathGenome.Internal.Specs.D05.M10.InvariantFactorComputation.Existence
import MathGenome.Internal.D05.Foundations.Division
import MathGenome.Internal.D05.M04.MatrixProduct
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

noncomputable section

namespace D05.M10.InvariantFactorComputation.Existence
open D05.M10.Smith

namespace Op
variable {K : Type*} [Field K] {m n : ℕ}

@[simp] theorem inverse_inverse (op : Operation K m n) : op.inverse.inverse = op := by
  cases op <;> simp [Operation.inverse]

theorem inverse_apply (op : Operation K m n)
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) : op.inverse.apply (op.apply M) = M := by
  cases op with
  | swapRows i j => ext a b; simp [Operation.inverse, Operation.apply]
  | swapCols i j => ext a b; simp [Operation.inverse, Operation.apply]
  | addRow i j h q =>
    ext a b
    by_cases ha : a = i
    · subst a; simp [Operation.inverse, Operation.apply, h.symm]
    · simp [Operation.inverse, Operation.apply, ha]
  | addCol i j h q =>
    ext a b
    by_cases hb : b = i
    · subst b; simp [Operation.inverse, Operation.apply, h.symm]
    · simp [Operation.inverse, Operation.apply, hb]
  | scaleRow i c =>
    ext a b
    by_cases ha : a = i <;> simp [Operation.inverse, Operation.apply, ha, ← mul_assoc,
      ← Polynomial.C_mul]
  | scaleCol j c =>
    ext a b
    by_cases hb : b = j <;> simp [Operation.inverse, Operation.apply, hb, ← mul_assoc,
      ← Polynomial.C_mul]

end Op

theorem operationInverse : D05.Specs.InvariantFactorComputation.Existence.operationInverse := by
  intro K _ m n op M
  exact ⟨Op.inverse_apply op M, by simpa using Op.inverse_apply op.inverse M⟩

@[simp] theorem run_nil {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) : run [] M = M := rfl

@[simp] theorem run_cons {K : Type*} [Field K] {m n : ℕ}
    (op : Operation K m n) (ops : List (Operation K m n))
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) :
    run (op :: ops) M = run ops (op.apply M) := rfl

theorem run_append {K : Type*} [Field K] {m n : ℕ}
    (xs ys : List (Operation K m n)) (M : Matrix (Fin m) (Fin n) (Polynomial K)) :
    run (xs ++ ys) M = run ys (run xs M) := List.foldl_append

theorem reachable_refl {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) : Reachable M M := ⟨[], rfl⟩

theorem reachable_step {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) (op : Operation K m n) :
    Reachable M (op.apply M) := ⟨[op], rfl⟩

theorem reachable_trans {K : Type*} [Field K] {m n : ℕ}
    {M N P : Matrix (Fin m) (Fin n) (Polynomial K)}
    (h : Reachable M N) (h' : Reachable N P) : Reachable M P := by
  obtain ⟨xs, rfl⟩ := h
  obtain ⟨ys, rfl⟩ := h'
  exact ⟨xs ++ ys, run_append xs ys M⟩

theorem remainderDescent : D05.Specs.InvariantFactorComputation.Existence.remainderDescent := by
  intro K _ a b ha h
  have hr : b % a ≠ 0 := fun hz => h (EuclideanDomain.mod_eq_zero.mp hz)
  exact ⟨hr, Polynomial.natDegree_lt_natDegree hr (Polynomial.degree_mod_lt b ha)⟩

theorem pivotTermination : D05.Specs.InvariantFactorComputation.Existence.pivotTermination := by
  intro K _
  exact InvImage.wf (fun p : {p : Polynomial K // p ≠ 0} => p.val.natDegree) Nat.lt_wfRel.wf

/-- Subtraction of the quotient is performed as a polynomial row addition. -/
theorem row_remainder {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) (i p : Fin m) (j : Fin n) (h : i ≠ p) :
    (Operation.apply (.addRow i p h (-(M i j / M p j))) M) i j = M i j % M p j := by
  simp only [Operation.apply, neg_mul, ← sub_eq_add_neg]
  simpa only [mul_comm, ite_true] using (EuclideanDomain.mod_eq_sub_mul_div _ _).symm

/-- Column version of quotient subtraction. -/
theorem col_remainder {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) (j p : Fin n) (i : Fin m) (h : j ≠ p) :
    (Operation.apply (.addCol j p h (-(M i j / M i p))) M) i j = M i j % M i p := by
  simp only [Operation.apply, neg_mul, ← sub_eq_add_neg]
  simpa only [mul_comm, ite_true] using (EuclideanDomain.mod_eq_sub_mul_div _ _).symm

theorem trailingEntryDescent :
    D05.Specs.InvariantFactorComputation.Existence.trailingEntryDescent := by
  intro K _ m n M i j ha hc hr hbad
  let A := (Operation.addRow 0 i.succ (Fin.succ_ne_zero i).symm 1).apply M
  have A00 : A 0 0 = M 0 0 := by simp [A, Operation.apply, hc]
  have A0j : A 0 j.succ = M i.succ j.succ := by simp [A, Operation.apply, hr]
  let op : Operation K (m+1) (n+1) := .addCol j.succ 0 (Fin.succ_ne_zero j)
    (-(A 0 j.succ / A 0 0))
  let B := op.apply A
  have hrem : B 0 j.succ = M i.succ j.succ % M 0 0 := by
    rw [show B 0 j.succ = A 0 j.succ % A 0 0 from
      col_remainder A j.succ 0 0 (Fin.succ_ne_zero j), A00, A0j]
  let N := (Operation.swapCols 0 j.succ).apply B
  have N00 : N 0 0 = M i.succ j.succ % M 0 0 := by
    simpa [N, Operation.apply] using hrem
  refine ⟨N, ?_, ?_⟩
  · exact reachable_trans (reachable_step M _) (reachable_trans (reachable_step A op)
      (reachable_step B (.swapCols 0 j.succ)))
  · rw [N00]
    exact remainderDescent K (M 0 0) (M i.succ j.succ) ha hbad

/-- Minimality is across the entire elementary orbit and all nonzero entries.
It is used only as a well-founded proof device, not as an assumed certificate. -/
def PivotMinimal {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)) : Prop :=
  M 0 0 ≠ 0 ∧ ∀ N, Reachable M N → ∀ i j, N i j ≠ 0 →
    (M 0 0).natDegree ≤ (N i j).natDegree

/-- Choose a reachable nonzero entry of least natural degree, and move it to
(0,0). This is a proof of existence using well-ordering of ℕ. -/
theorem exists_minimal_pivot {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)) (hne : M ≠ 0) :
    ∃ A, Reachable M A ∧ PivotMinimal A := by
  classical
  have hex : ∃ d : ℕ, ∃ N, Reachable M N ∧ ∃ i j, N i j ≠ 0 ∧ (N i j).natDegree = d := by
    have he : ∃ i j, M i j ≠ 0 := by
      by_contra! h
      exact hne (Matrix.ext h)
    obtain ⟨i, j, hij⟩ := he
    exact ⟨_, M, reachable_refl M, i, j, hij, rfl⟩
  obtain ⟨N, hMN, i, j, hij, hd⟩ := Nat.find_spec hex
  let A := (Operation.swapCols 0 j).apply ((Operation.swapRows 0 i).apply N)
  have hNA : Reachable N A := reachable_trans (reachable_step N (.swapRows 0 i))
    (reachable_step _ (.swapCols 0 j))
  have hA : A 0 0 = N i j := by simp [A, Operation.apply]
  refine ⟨A, reachable_trans hMN hNA, ?_, ?_⟩
  · rwa [hA]
  · intro B hAB k l hkl
    rw [hA, hd]
    exact Nat.find_min' hex ⟨B, reachable_trans hMN (reachable_trans hNA hAB), k, l, hkl, rfl⟩

/-- Minimality propagates when operations preserve the pivot. -/
theorem PivotMinimal.of_reachable {K : Type*} [Field K] {m n : ℕ}
    {M N : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)}
    (hM : PivotMinimal M) (hMN : Reachable M N) (h00 : N 0 0 = M 0 0) :
    PivotMinimal N := by
  refine ⟨by rw [h00]; exact hM.1, ?_⟩
  intro P hNP i j hij
  rw [h00]
  exact hM.2 P (reachable_trans hMN hNP) i j hij

/-- A least-degree pivot divides every entry of its column. -/
theorem PivotMinimal.dvd_col {K : Type*} [Field K] {m n : ℕ}
    {M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)}
    (hM : PivotMinimal M) (i : Fin (m+1)) : M 0 0 ∣ M i 0 := by
  by_cases hi : i = 0
  · subst i; exact dvd_rfl
  by_contra h
  have hd := remainderDescent K (M 0 0) (M i 0) hM.1 h
  let op : Operation K (m+1) (n+1) := .addRow i 0 hi (-(M i 0 / M 0 0))
  have he : op.apply M i 0 = M i 0 % M 0 0 := row_remainder M i 0 0 hi
  have hlow := hM.2 (op.apply M) (reachable_step M op) i 0 (by rw [he]; exact hd.1)
  rw [he] at hlow
  exact (Nat.not_lt_of_ge hlow) hd.2

/-- The corresponding first-row divisibility statement. -/
theorem PivotMinimal.dvd_row {K : Type*} [Field K] {m n : ℕ}
    {M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)}
    (hM : PivotMinimal M) (j : Fin (n+1)) : M 0 0 ∣ M 0 j := by
  by_cases hj : j = 0
  · subst j; exact dvd_rfl
  by_contra h
  have hd := remainderDescent K (M 0 0) (M 0 j) hM.1 h
  let op : Operation K (m+1) (n+1) := .addCol j 0 hj (-(M 0 j / M 0 0))
  have he : op.apply M 0 j = M 0 j % M 0 0 := col_remainder M j 0 0 hj
  have hlow := hM.2 (op.apply M) (reachable_step M op) 0 j (by rw [he]; exact hd.1)
  rw [he] at hlow
  exact (Nat.not_lt_of_ge hlow) hd.2

/-- Clear any finite set of rows below a minimal pivot. Each step is one
quotient subtraction; minimality forces its remainder to vanish. -/
theorem clear_column_set {K : Type*} [Field K] {m n : ℕ} (S : Finset (Fin m))
    (M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)) (hM : PivotMinimal M) :
    ∃ N, Reachable M N ∧ N 0 0 = M 0 0 ∧ ∀ i ∈ S, N i.succ 0 = 0 := by
  classical
  induction S using Finset.induction_on generalizing M with
  | empty => exact ⟨M, reachable_refl M, rfl, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨N, hMN, h00, hS⟩ := ih M hM
    have hN := hM.of_reachable hMN h00
    let op : Operation K (m+1) (n+1) := .addRow i.succ 0 (Fin.succ_ne_zero i)
      (-(N i.succ 0 / N 0 0))
    have hz : op.apply N i.succ 0 = 0 := by
      rw [row_remainder N i.succ 0 0 (Fin.succ_ne_zero i)]
      exact EuclideanDomain.mod_eq_zero.mpr (hN.dvd_col i.succ)
    refine ⟨op.apply N, reachable_trans hMN (reachable_step N op), ?_, ?_⟩
    · simpa [op, Operation.apply, (Fin.succ_ne_zero i).symm] using h00
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hz
      · by_cases hki : k = i
        · subst k; exact hz
        · simpa [op, Operation.apply, hki] using hS k hk

/-- Clearing first-row entries leaves the already cleared first column fixed. -/
theorem clear_row_set {K : Type*} [Field K] {m n : ℕ} (S : Finset (Fin n))
    (M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)) (hM : PivotMinimal M)
    (hc : ∀ i : Fin m, M i.succ 0 = 0) :
    ∃ N, Reachable M N ∧ N 0 0 = M 0 0 ∧ (∀ i : Fin m, N i.succ 0 = 0) ∧
      ∀ j ∈ S, N 0 j.succ = 0 := by
  classical
  induction S using Finset.induction_on generalizing M with
  | empty => exact ⟨M, reachable_refl M, rfl, hc, by simp⟩
  | @insert j S hj ih =>
    obtain ⟨N, hMN, h00, hcN, hS⟩ := ih M hM hc
    have hN := hM.of_reachable hMN h00
    let op : Operation K (m+1) (n+1) := .addCol j.succ 0 (Fin.succ_ne_zero j)
      (-(N 0 j.succ / N 0 0))
    have hz : op.apply N 0 j.succ = 0 := by
      rw [col_remainder N j.succ 0 0 (Fin.succ_ne_zero j)]
      exact EuclideanDomain.mod_eq_zero.mpr (hN.dvd_row j.succ)
    refine ⟨op.apply N, reachable_trans hMN (reachable_step N op), ?_, ?_, ?_⟩
    · simpa [op, Operation.apply, (Fin.succ_ne_zero j).symm] using h00
    · intro i
      simpa [op, Operation.apply, (Fin.succ_ne_zero j).symm] using hcN i
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hz
      · by_cases hkj : k = j
        · subst k; exact hz
        · simpa [op, Operation.apply, hkj] using hS k hk

/-- An isolated minimal pivot divides the trailing rectangle; otherwise the
explicit three-operation descent contradicts its minimal degree. -/
theorem PivotMinimal.dvd_trailing {K : Type*} [Field K] {m n : ℕ}
    {M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)} (hM : PivotMinimal M)
    (hc : ∀ i : Fin m, M i.succ 0 = 0) (hr : ∀ j : Fin n, M 0 j.succ = 0)
    (i : Fin m) (j : Fin n) : M 0 0 ∣ M i.succ j.succ := by
  by_contra h
  obtain ⟨N, hMN, hne, hlt⟩ := trailingEntryDescent K m n M i j hM.1 hc hr h
  exact (Nat.not_lt_of_ge (hM.2 N hMN 0 0 hne)) hlt

/-- First stage of Smith reduction, before normalizing the pivot or recursing. -/
theorem isolate_pivot {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)) (hne : M ≠ 0) :
    ∃ N, Reachable M N ∧ N 0 0 ≠ 0 ∧
      (∀ i : Fin m, N i.succ 0 = 0) ∧ (∀ j : Fin n, N 0 j.succ = 0) ∧
      (∀ i : Fin m, ∀ j : Fin n, N 0 0 ∣ N i.succ j.succ) := by
  classical
  obtain ⟨A, hMA, hA⟩ := exists_minimal_pivot M hne
  obtain ⟨B, hAB, hB00, hc⟩ := clear_column_set Finset.univ A hA
  have hcB : ∀ i : Fin m, B i.succ 0 = 0 := fun i => hc i (Finset.mem_univ i)
  have hB := hA.of_reachable hAB hB00
  obtain ⟨C, hBC, hC00, hcC, hr⟩ := clear_row_set Finset.univ B hB hcB
  have hrC : ∀ j : Fin n, C 0 j.succ = 0 := fun j => hr j (Finset.mem_univ j)
  have hC := hB.of_reachable hBC hC00
  exact ⟨C, reachable_trans hMA (reachable_trans hAB hBC), hC.1,
    hcC, hrC, hC.dvd_trailing hcC hrC⟩

/-- Adjoin an isolated upper-left entry to a smaller rectangular matrix. -/
def border {K : Type*} [Field K] {m n : ℕ} (a : Polynomial K)
    (B : Matrix (Fin m) (Fin n) (Polynomial K)) :
    Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K) :=
  Fin.cases (Fin.cases a (fun _ => 0)) (fun i => Fin.cases 0 (B i))

@[simp] theorem border_zero_zero {K : Type*} [Field K] {m n : ℕ}
    (a : Polynomial K) (B : Matrix (Fin m) (Fin n) (Polynomial K)) : border a B 0 0 = a := rfl
@[simp] theorem border_succ_zero {K : Type*} [Field K] {m n : ℕ}
    (a : Polynomial K) (B : Matrix (Fin m) (Fin n) (Polynomial K)) (i : Fin m) :
    border a B i.succ 0 = 0 := rfl
@[simp] theorem border_zero_succ {K : Type*} [Field K] {m n : ℕ}
    (a : Polynomial K) (B : Matrix (Fin m) (Fin n) (Polynomial K)) (j : Fin n) :
    border a B 0 j.succ = 0 := rfl
@[simp] theorem border_succ_succ {K : Type*} [Field K] {m n : ℕ}
    (a : Polynomial K) (B : Matrix (Fin m) (Fin n) (Polynomial K)) (i : Fin m) (j : Fin n) :
    border a B i.succ j.succ = B i j := rfl

/-- Normalize the isolated pivot using only one permitted scalar rescaling. -/
theorem split_monic_pivot {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K)) (hne : M ≠ 0) :
    ∃ (a : Polynomial K) (B : Matrix (Fin m) (Fin n) (Polynomial K)),
      Reachable M (border a B) ∧ a ≠ 0 ∧ a.Monic ∧ ∀ i j, a ∣ B i j := by
  obtain ⟨N, hMN, ha, hc, hr, hd⟩ := isolate_pivot M hne
  let u : Kˣ := Units.mk0 (N 0 0).leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr ha)
  let a := Polynomial.C (↑u⁻¹ : K) * N 0 0
  let B : Matrix (Fin m) (Fin n) (Polynomial K) := fun i j => N i.succ j.succ
  have ham : a.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by
    change (↑u⁻¹ : K) * (↑u : K) = 1
    exact Units.inv_mul u)
  have had : a ∣ N 0 0 := by
    refine ⟨Polynomial.C (↑u : K), ?_⟩
    dsimp [a]
    calc
      N 0 0 = (Polynomial.C (↑u⁻¹ : K) * Polynomial.C (↑u : K)) * N 0 0 := by
        simp [← Polynomial.C_mul]
      _ = _ := by ring
  have heq : (Operation.scaleRow 0 u⁻¹).apply N = border a B := by
    apply Matrix.ext
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp [Operation.apply, hr]
    · simpa [Operation.apply] using hc i
    · simp [Operation.apply, B, border]
  refine ⟨a, B, ?_, ham.ne_zero, ham, ?_⟩
  · exact reachable_trans hMN (heq ▸ reachable_step N (.scaleRow 0 u⁻¹))
  · intro i j
    exact dvd_trans had (hd i j)

/-- Extend an operation on the trailing rectangle, fixing row and column 0. -/
def liftOperation {K : Type*} [Field K] {m n : ℕ} :
    Operation K m n → Operation K (m+1) (n+1)
  | .swapRows i j => .swapRows i.succ j.succ
  | .swapCols i j => .swapCols i.succ j.succ
  | .addRow i j h q => .addRow i.succ j.succ (fun he => h (Fin.succ_injective _ he)) q
  | .addCol i j h q => .addCol i.succ j.succ (fun he => h (Fin.succ_injective _ he)) q
  | .scaleRow i c => .scaleRow i.succ c
  | .scaleCol j c => .scaleCol j.succ c

theorem lift_apply {K : Type*} [Field K] {m n : ℕ} (op : Operation K m n)
    (a : Polynomial K) (B : Matrix (Fin m) (Fin n) (Polynomial K)) :
    (liftOperation op).apply (border a B) = border a (op.apply B) := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    cases op <;> simp [liftOperation, Operation.apply, Equiv.swap_apply_def, border, eq_comm] <;>
    (try split_ifs) <;> simp_all

theorem lift_run {K : Type*} [Field K] {m n : ℕ} (ops : List (Operation K m n))
    (a : Polynomial K) (B : Matrix (Fin m) (Fin n) (Polynomial K)) :
    run (ops.map liftOperation) (border a B) = border a (run ops B) := by
  induction ops generalizing B with
  | nil => rfl
  | cons op ops ih => simp only [List.map_cons, run_cons, lift_apply, ih]

/-- All permitted operations preserve any common polynomial divisor. -/
theorem operation_preserves_divisor {K : Type*} [Field K] {m n : ℕ}
    (op : Operation K m n) (a : Polynomial K)
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) (h : ∀ i j, a ∣ M i j) :
    ∀ i j, a ∣ op.apply M i j := by
  intro i j
  cases op with
  | swapRows p q => exact h _ _
  | swapCols p q => exact h _ _
  | addRow p q hp c =>
    dsimp [Operation.apply]
    split
    · exact dvd_add (h _ _) (dvd_mul_of_dvd_right (h _ _) _)
    · exact h _ _
  | addCol p q hp c =>
    dsimp [Operation.apply]
    split
    · exact dvd_add (h _ _) (dvd_mul_of_dvd_right (h _ _) _)
    · exact h _ _
  | scaleRow p c =>
    dsimp [Operation.apply]
    split
    · exact dvd_mul_of_dvd_right (h _ _) _
    · exact h _ _
  | scaleCol p c =>
    dsimp [Operation.apply]
    split
    · exact dvd_mul_of_dvd_right (h _ _) _
    · exact h _ _

theorem run_preserves_divisor {K : Type*} [Field K] {m n : ℕ}
    (ops : List (Operation K m n)) (a : Polynomial K)
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) (h : ∀ i j, a ∣ M i j) :
    ∀ i j, a ∣ run ops M i j := by
  induction ops generalizing M with
  | nil => exact h
  | cons op ops ih => exact ih (op.apply M) (operation_preserves_divisor op a M h)

/-- The zero matrix has an empty nonzero factor list, in any shape. -/
theorem isSmith_zero {K : Type*} [Field K] (m n : ℕ) :
    IsSmith (0 : Matrix (Fin m) (Fin n) (Polynomial K)) := by
  refine ⟨0, fun _ => 0, Nat.zero_le _, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · intro i j; simp

/-- Prepending a monic nonzero common divisor retains the Smith divisibility
chain. Common divisibility is checked on the final trailing rectangle. -/
theorem isSmith_border {K : Type*} [Field K] {m n : ℕ}
    (a : Polynomial K) (B : Matrix (Fin m) (Fin n) (Polynomial K))
    (ha : a ≠ 0) (ham : a.Monic) (hB : IsSmith B) (hd : ∀ i j, a ∣ B i j) :
    IsSmith (border a B) := by
  obtain ⟨r, d, hr, hnon, hzero, hdiv, he⟩ := hB
  let e : ℕ → Polynomial K := fun i => Nat.casesOn i a d
  have ha0 : a ∣ d 0 := by
    by_cases h : r = 0
    · rw [hzero 0 (by omega)]
      exact dvd_zero a
    · have hm : 0 < m := by omega
      have hn : 0 < n := by omega
      let i : Fin m := ⟨0, hm⟩
      let j : Fin n := ⟨0, hn⟩
      have hij : B i j = d 0 := by simpa [i, j] using he i j
      rw [← hij]
      exact hd i j
  refine ⟨r+1, e, by omega, ?_, ?_, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero => exact ⟨ha, ham⟩
    | succ i => exact hnon i (by omega)
  · intro i hi
    cases i with
    | zero => omega
    | succ i => exact hzero i (by omega)
  · intro i
    cases i with
    | zero => exact ha0
    | succ i => exact hdiv i
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [border, e]
    · simp [border]
    · simp [border]
    · simpa [border, e] using he i j

/-- Smith reduction over the original field's polynomial ring. The outer
induction removes one row and one column; the inner pivot argument is justified
by well-founded polynomial degree. Every operation list uses only the six
constructors in the independent specification. -/
theorem smithReduction : D05.Specs.InvariantFactorComputation.Existence.smithReduction := by
  intro K _ m
  induction m with
  | zero =>
    intro n M
    have h : M = 0 := Matrix.ext (fun i => Fin.elim0 i)
    exact ⟨[], h ▸ isSmith_zero 0 n⟩
  | succ m ih =>
    intro n M
    cases n with
    | zero =>
      have h : M = 0 := Matrix.ext (fun _ j => Fin.elim0 j)
      exact ⟨[], h ▸ isSmith_zero (m+1) 0⟩
    | succ n =>
      by_cases hz : M = 0
      · exact ⟨[], hz ▸ isSmith_zero (m+1) (n+1)⟩
      · obtain ⟨a, B, ⟨xs, hxs⟩, ha, ham, hd⟩ := split_monic_pivot M hz
        obtain ⟨ys, hys⟩ := ih n B
        refine ⟨xs ++ ys.map liftOperation, ?_⟩
        rw [run_append, hxs, lift_run]
        exact isSmith_border a (run ys B) ha ham hys (run_preserves_divisor ys a B hd)

end D05.M10.InvariantFactorComputation.Existence
