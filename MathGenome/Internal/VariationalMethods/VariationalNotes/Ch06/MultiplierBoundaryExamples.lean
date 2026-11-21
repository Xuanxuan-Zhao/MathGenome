import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.MultiplierBoundaryExamples
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.SmoothConstraintModels
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! The scalar boundary examples of paper.tex §v06-05, using the actual
Fréchet derivative systems of SmoothConstraintModels. -/
noncomputable section
universe u v
namespace VariationalNotes.Ch06

def StrictComplementarity : Specs.StrictComplementarityType := @Specs.StrictComplementarity

private lemma square_fderiv_zero :
    fderiv ℝ (fun x : ℝ => x ^ 2) 0 = 0 := by
  simp [fderiv_pow_ring]

private lemma neg_fderiv_zero :
    fderiv ℝ (fun x : ℝ => -x) 0 = -ContinuousLinearMap.id ℝ ℝ := by
  exact (hasFDerivAt_id (0 : ℝ)).neg.fderiv

private lemma real_id_ne_zero : ContinuousLinearMap.id ℝ ℝ ≠ 0 := by
  intro h
  have := congrArg (fun l : ℝ →L[ℝ] ℝ => l 1) h
  norm_num at this

theorem boundary_examples_smooth : Specs.boundary_examples_smooth := by
  unfold Specs.boundary_examples_smooth Specs.SmoothConstraintData
  refine ⟨⟨isOpen_univ, ?_, ?_, ?_⟩, ⟨isOpen_univ, ?_, ?_, ?_⟩,
    ⟨isOpen_univ, ?_, ?_, ?_⟩⟩
  all_goals fun_prop

theorem duplicate_minimum : Specs.duplicate_minimum := by
  intro x hx
  have hx0 := hx.2.1 (0 : Fin 2)
  dsimp
  linarith

theorem duplicate_mfcq : Specs.duplicate_mfcq := by
  refine ⟨by simp [Specs.feasibleSet], ?_, -1, ?_, ?_⟩
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact Subsingleton.elim _ _
  · intro i hi
    simp

theorem duplicate_kkt_iff : Specs.duplicate_kkt_iff := by
  intro lam
  simp only [Specs.KKT, Specs.feasibleSet, Set.mem_ofPred_eq, Set.mem_univ,
    le_refl, implies_true, and_true, true_and, mul_zero,
    neg_fderiv_zero, fderiv_fun_id, Fin.sum_univ_two, Fin.sum_univ_zero, add_zero]
  constructor
  · rintro ⟨hn, hs⟩
    refine ⟨hn, ?_⟩
    have he := congrArg (fun l : ℝ →L[ℝ] ℝ => l 1) hs
    simp at he
    linarith
  · rintro ⟨hn, hs⟩
    refine ⟨hn, ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    simp
    nlinarith [congrArg (fun a : ℝ => a * x) hs]

theorem duplicate_multiplier_compact_nonunique : Specs.duplicate_multiplier_compact_nonunique := by
  have hset : {lam : Fin 2 → ℝ | Specs.KKT Set.univ (fun x : ℝ => -x)
      (fun (_ : Fin 2) (x : ℝ) => x) (fun (_ : Fin 0) (_ : ℝ) => 0)
      0 lam (fun (_ : Fin 0) => 0)} =
      Set.Icc (fun (_ : Fin 2) => (0 : ℝ)) (fun _ => 1) ∩
        {lam : Fin 2 → ℝ | lam 0 + lam 1 = 1} := by
    ext lam
    rw [Set.mem_ofPred_eq, duplicate_kkt_iff]
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Pi.le_def]
    constructor
    · rintro ⟨hn, hs⟩
      refine ⟨⟨hn, ?_⟩, hs⟩
      intro i
      fin_cases i <;> dsimp <;> linarith [hn 0, hn 1]
    · rintro ⟨⟨hn, _⟩, hs⟩
      exact ⟨hn, hs⟩
  constructor
  · rw [hset]
    exact isCompact_Icc.inter_right
      (isClosed_eq ((continuous_apply 0).add (continuous_apply 1)) continuous_const)
  · refine ⟨![0, 1], ![1, 0], ?_, ?_, ?_⟩
    · rw [duplicate_kkt_iff]
      norm_num [Fin.forall_fin_two]
    · rw [duplicate_kkt_iff]
      norm_num [Fin.forall_fin_two]
    · intro he
      have := congrFun he 0
      norm_num at this

theorem squareObjective_minimum : Specs.squareObjective_minimum := by
  intro x _
  simpa using sq_nonneg x

theorem squareObjective_licq : Specs.squareObjective_licq := by
  constructor
  · simp [Specs.feasibleSet]
  · let i : {i : Fin 1 // i ∈ Specs.activeSet (fun (_ : Fin 1) (x : ℝ) => x) 0} :=
      ⟨0, rfl⟩
    apply LinearIndependent.of_subsingleton (i := Sum.inl i)
    simpa using real_id_ne_zero

theorem squareObjective_kkt_iff : Specs.squareObjective_kkt_iff := by
  intro lam
  simp only [Specs.KKT, Specs.feasibleSet, Set.mem_ofPred_eq, Set.mem_univ,
    le_refl, implies_true, mul_zero, and_true, true_and,
    square_fderiv_zero, fderiv_fun_id, Fin.sum_univ_one, Fin.sum_univ_zero,
    add_zero, zero_add]
  constructor
  · rintro ⟨_, hs⟩
    have he := congrArg (fun l : ℝ →L[ℝ] ℝ => l 1) hs
    simp at he
    ext i
    fin_cases i
    exact he
  · rintro rfl
    simp

theorem squareObjective_not_strict : Specs.squareObjective_not_strict := by
  refine ⟨(squareObjective_kkt_iff 0).mpr rfl, ?_⟩
  intro hs
  have := hs.2.2 (0 : Fin 1) rfl
  norm_num at this

theorem squaredConstraint_feasible : Specs.squaredConstraint_feasible := by
  ext x
  simp only [Specs.feasibleSet, Set.mem_ofPred_eq, Set.mem_univ, true_and,
    forall_const, Set.mem_singleton_iff]
  exact ⟨fun hx => by nlinarith [sq_nonneg x], fun hx => by simp [hx]⟩

theorem squaredConstraint_minimum : Specs.squaredConstraint_minimum := by
  rw [Specs.squaredConstraint_minimum, squaredConstraint_feasible]
  intro x hx
  simpa using (Set.mem_singleton_iff.mp hx).ge

theorem squaredConstraint_no_kkt : Specs.squaredConstraint_no_kkt := by
  intro lam hk
  have hs := hk.2.2.2
  simp only [fderiv_fun_id, square_fderiv_zero, smul_zero, Fin.sum_univ_one,
    Fin.sum_univ_zero, add_zero] at hs
  exact real_id_ne_zero hs

theorem squaredConstraint_abnormal : Specs.squaredConstraint_abnormal := by
  simp [Specs.squaredConstraint_abnormal, Specs.FritzJohn, Specs.feasibleSet,
    square_fderiv_zero]

end VariationalNotes.Ch06
