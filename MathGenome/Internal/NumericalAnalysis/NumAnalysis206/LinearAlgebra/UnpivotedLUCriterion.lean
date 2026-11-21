import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.UnpivotedLUCriterion
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.PivotedLU
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.UnpivotedLU
open NumAnalysis206.MatrixDefinitions
universe u
variable {K : Type u} [Field K]

theorem schur_matches_eliminate : Specs.NumAnalysis206.UnpivotedLU.schur_matches_eliminate := by
  intro K _ n A i j
  simp [schur, PivotedLU.eliminate, PivotedLU.multipliers]

/-- Clearing the first column preserves the determinant; expanding that
column then gives the first pivot times the Schur determinant. -/
theorem det_eq_pivot_mul_schur {n : ℕ} (A : Mat K (n + 1) (n + 1))
    (hp : A 0 0 ≠ 0) : A.det = A 0 0 * (schur A).det := by
  let E := PivotedLU.eliminate A 0 0 0
  have hdet : E.det = A.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => -PivotedLU.multipliers A 0 0 0 i) 0
    · simp [PivotedLU.multipliers]
    · intro i j
      simp [E, PivotedLU.eliminate, sub_eq_add_neg]
  rw [← hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hzero : ∀ i : Fin n, E i.succ 0 = 0 := by
    intro i
    exact (PivotedLU.eliminate_pivot A 0 0 0 hp).2 i.succ (Fin.succ_pos i)
  simp only [hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  have hhead : E 0 0 = A 0 0 := (PivotedLU.eliminate_pivot A 0 0 0 hp).1
  have htail : E.submatrix Fin.succ Fin.succ = schur A := by
    ext i j
    exact (schur_matches_eliminate A i j).symm
  rw [hhead, htail]

@[simp] theorem leadingMinor_one {n : ℕ} (A : Mat K (n + 1) (n + 1))
    (h : 1 ≤ n + 1) : leadingMinor A 1 h = A 0 0 := by
  simp [leadingMinor, Matrix.det_unique]

@[simp] theorem leadingMinor_full {n : ℕ} (A : Mat K n n) :
    leadingMinor A n le_rfl = A.det := by
  rfl

/-- Leading blocks commute with the row-subtraction update. -/
theorem schur_leading {n k : ℕ} (A : Mat K (n + 1) (n + 1)) (h : k ≤ n) :
    schur (A.submatrix (Fin.castLE (Nat.succ_le_succ h))
      (Fin.castLE (Nat.succ_le_succ h))) =
    (schur A).submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  rfl

theorem leadingMinor_succ {n k : ℕ} (A : Mat K (n + 1) (n + 1))
    (h : k ≤ n) (hp : A 0 0 ≠ 0) :
    leadingMinor A (k + 1) (Nat.succ_le_succ h) =
      A 0 0 * leadingMinor (schur A) k h := by
  unfold leadingMinor
  rw [det_eq_pivot_mul_schur _ (by simpa using hp), schur_leading]
  rfl

/-- Nonvanishing minors construct successful earlier steps; the converse
uses the same determinant identity on every leading block. -/
theorem criterion : Specs.NumAnalysis206.UnpivotedLU.criterion := by
  intro K _ n
  induction n with
  | zero =>
    intro A
    constructor
    · intro _ k hk hkn; omega
    · intro _; trivial
  | succ n ih =>
    cases n with
    | zero =>
      intro A
      constructor
      · intro _ k hk hkn; omega
      · intro _; trivial
    | succ n =>
      intro A
      change (A 0 0 ≠ 0 ∧ Succeeds (schur A)) ↔ _
      constructor
      · rintro ⟨hp, hs⟩ k hk hkn
        cases k with
        | zero => omega
        | succ k =>
          rw [leadingMinor_succ A (by omega) hp]
          apply mul_ne_zero hp
          by_cases hk0 : k = 0
          · subst k
            simp [leadingMinor]
          · exact (ih (schur A)).mp hs k (by omega) (by omega)
      · intro hm
        have hp : A 0 0 ≠ 0 := by
          simpa using hm 1 (by omega) (by omega)
        refine ⟨hp, (ih (schur A)).mpr ?_⟩
        intro k hk hkn
        have h := hm (k + 1) (by omega) (by omega)
        rw [leadingMinor_succ A (by omega) hp] at h
        exact (mul_ne_zero_iff.mp h).2

/-- The final diagonal is allowed to vanish; it vanishes precisely in the
singular case, after the required earlier divisions have succeeded. -/
theorem terminal_criterion : Specs.NumAnalysis206.UnpivotedLU.terminal_criterion := by
  intro K _ n
  induction n with
  | zero =>
    intro A _
    simp [terminal, Matrix.det_unique]
  | succ n ih =>
    intro A hs
    obtain ⟨hp, ht⟩ := hs
    change terminal (schur A) ≠ 0 ↔ A.det ≠ 0
    rw [det_eq_pivot_mul_schur A hp, mul_ne_zero_iff]
    exact (ih (schur A) ht).trans (by simp [hp])

theorem boundary_cases : Specs.NumAnalysis206.UnpivotedLU.boundary_cases := by
  intro K _
  constructor
  · intro A
    exact ⟨True.intro, Matrix.det_isEmpty⟩
  · intro A
    exact ⟨True.intro, rfl⟩

theorem exchange_example : Specs.NumAnalysis206.UnpivotedLU.exchange_example := by
  intro K _
  refine ⟨?_, ?_, ?_⟩
  · apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simp [exchange, Matrix.det_fin_two]
  · simp [exchange]
  · simp [Succeeds, exchange, Matrix.cons_val_zero]

theorem bare_lu_example : Specs.NumAnalysis206.UnpivotedLU.bare_lu_example := by
  intro K _
  refine ⟨?_, ?_, Matrix.one_mul _, ?_⟩
  · constructor
    · intro i j hij
      have : i ≠ j := by omega
      simp [this]
    · intro i
      simp
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [zeroOneDiagonal]
  · simp [Succeeds, zeroOneDiagonal, Matrix.cons_val_zero]

end NumAnalysis206.UnpivotedLU
