import MathGenome.Internal.Specs.D05.M01.Consistency
import MathGenome.Internal.D05.M01.Elimination
import MathGenome.Internal.D05.M01.SolutionInvariance
import MathGenome.Internal.D05.M04.RankBridge

/-! Consistency of a linear system, K05.01.consistency.
We use the proved backward reduction, which preserves every pivot position,
and solve the reduced system with every free coordinate zero. -/
namespace D05.M01.Consistency

open scoped BigOperators Matrix
universe u
variable {K : Type u} [Field K] {m n : ℕ}

/-- In a reduced augmentation with no last-column pivot, putting the RHS
at the coefficient pivots and zero at the free coordinates solves the system. -/
theorem reduced_has_solution (M : Matrix (Fin m) (Fin (n + 1)) K)
    (hr : M.IsReducedRowEchelon)
    (hn : ∀ i, ¬ M.IsLeadingEntry i (Fin.last n)) :
    ∃ x : Fin n → K, System.IsSolution (fun i j => M i j.castSucc)
      (fun i => M i (Fin.last n)) x := by
  classical
  let x : Fin n → K := fun j =>
    ∑ i : Fin m, if M.IsLeadingEntry i j.castSucc then M i (Fin.last n) else 0
  refine ⟨x, (System.solution_iff_rows _ _ _).mpr ?_⟩
  intro r
  change (∑ j : Fin n, M r j.castSucc *
    ∑ i : Fin m, if M.IsLeadingEntry i j.castSucc then M i (Fin.last n) else 0) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hoff : ∀ i : Fin m, i ≠ r →
      (∑ j : Fin n, M r j.castSucc *
        (if M.IsLeadingEntry i j.castSucc then M i (Fin.last n) else 0)) = 0 := by
    intro i hir
    apply Finset.sum_eq_zero
    intro j _
    by_cases hij : M.IsLeadingEntry i j.castSucc
    · rw [ite_eq_left hij, hr.eq_zero_of_ne_of_isLeadingEntry hir.symm hij, zero_mul]
    · rw [ite_eq_right hij, mul_zero]
  rw [Finset.sum_eq_single r (fun i _ hir => hoff i hir) (by simp)]
  by_cases hz : M r = 0
  · have hzero : ∀ c, M r c = 0 := fun c => congrFun hz c
    simp only [hzero, zero_mul, Finset.sum_const_zero]
  · obtain ⟨c, hc⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp hz
    have hclast : c ≠ Fin.last n := by
      intro heq
      subst c
      exact hn r hc
    obtain ⟨p, hp⟩ := Fin.eq_castSucc_of_ne_last hclast
    subst c
    rw [Finset.sum_eq_single p]
    · rw [ite_eq_left hc, hr.eq_one hc, one_mul]
    · intro j _ hjp
      have hj : ¬ M.IsLeadingEntry r j.castSucc := by
        intro hj
        exact hjp (Fin.castSucc_inj.mp (hj.unique hc))
      rw [ite_eq_right hj, mul_zero]
    · simp

/-- An echelon augmentation is solvable exactly when it has no contradiction row. -/
theorem echelon_consistent_iff : ConsistencySpec.echelon_consistent_iff := by
  intro K _ m n A b he
  constructor
  · rintro ⟨x, hx⟩ i hi
    have hrow := (System.solution_iff_rows A b x).mp hx i
    have hz : ∀ j, A i j = 0 := fun j => congrFun hi j
    simpa only [hz, zero_mul, Finset.sum_const_zero] using hrow.symm
  · intro hn
    let M := System.augmentedMatrix A b
    have hnM : ∀ i, ¬ M.IsLeadingEntry i (Fin.last n) := by
      intro i hi
      obtain ⟨hai, hbi⟩ := (Echelon.augmented_pivot_last_iff A b i).mp hi
      exact hbi (hn i hai)
    obtain ⟨ops, hr, hp⟩ := Elimination.Backward.exists_reduced_same_pivots M he
    obtain ⟨x, hx⟩ := reduced_has_solution (Elimination.applyOperations ops M) hr
      (fun i hi => hnM i ((hp i (Fin.last n)).mp hi))
    refine ⟨x, ?_⟩
    exact (SolutionInvariance.sequence_preserves_solutions ops A b x).mp hx

/-- Row operations preserve the full solution set, so the same test applies to
any echelon form obtained from the original augmented matrix. -/
theorem echelon_form_criterion : ConsistencySpec.echelon_form_criterion := by
  intro K _ m n A b ops he
  let M := Elimination.applyOps ops (System.augmentedMatrix A b)
  let C : Matrix (Fin m) (Fin n) K := fun i j => M i j.castSucc
  let d : Fin m → K := fun i => M i (Fin.last n)
  have haug : System.augmentedMatrix C d = M :=
    SolutionInvariance.reconstruct_augmented M
  have heC : (System.augmentedMatrix C d).IsRowEchelon := by
    rw [haug]
    exact he
  have htest := echelon_consistent_iff C d heC
  have hsol : (∃ x, System.IsSolution A b x) ↔ ∃ x, System.IsSolution C d x := by
    exact exists_congr (fun x =>
      (SolutionInvariance.sequence_preserves_solutions ops A b x).symm)
  exact hsol.trans (htest.trans (by
    simp only [C, funext_iff, Pi.zero_apply]
    rfl))

theorem exists_echelon_test : ConsistencySpec.exists_echelon_test := by
  intro K _ m n A b
  obtain ⟨ops, he⟩ := Elimination.exists_echelon (System.augmentedMatrix A b)
  exact ⟨ops, he, echelon_form_criterion A b ops he⟩

theorem consistent_iff_mem_column_span : ConsistencySpec.consistent_iff_mem_column_span := by
  intro K _ m n A b
  exact (D05.M04.RankBridge.mem_column_span_iff A b).symm

end D05.M01.Consistency
