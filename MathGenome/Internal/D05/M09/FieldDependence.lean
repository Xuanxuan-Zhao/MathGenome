import MathGenome.Internal.Specs.D05.M09.FieldDependence
import MathGenome.Internal.D05.M09.Diagonalizable
import MathGenome.Internal.D05.M09.EigenspaceCriterion
import MathGenome.Internal.D05.M08.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! K05.09.field_dependence: explicit field and multiplicity counterexamples. -/
noncomputable section
namespace D05.M09.FieldDependence
open Specs.D05.M09.FieldDependence

private theorem rotation_apply (K : Type*) [Field K] (v : Fin 2 → K) :
    rotation K v = ![-v 1, v 0] := by
  ext i
  fin_cases i <;> simp [rotation, rotationMatrix, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

private theorem jordan_apply (K : Type*) [Field K] (v : Fin 2 → K) :
    jordan K v = ![v 0 + v 1, v 1] := by
  ext i
  fin_cases i <;> simp [jordan, jordanMatrix, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

theorem rotation_charpoly : Specs.D05.M09.FieldDependence.rotation_charpoly := by
  intro K _
  rw [rotation, Matrix.charpoly_mulVecLin, Matrix.charpoly_fin_two]
  simp [rotationMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.det_fin_two]

theorem rotation_real_no_roots : Specs.D05.M09.FieldDependence.rotation_real_no_roots := by
  intro x
  rw [rotation_charpoly]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith [sq_nonneg x]

theorem rotation_real_no_eigenvalues :
    Specs.D05.M09.FieldDependence.rotation_real_no_eigenvalues := by
  intro μ h
  obtain ⟨v, hv, hn⟩ := h.exists_hasEigenvector
  have he := Module.End.mem_eigenspace_iff.mp hv
  rw [rotation_apply] at he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.smul_apply, smul_eq_mul] at h0 h1
  have hp : (μ ^ 2 + 1) * v 1 = 0 := by
    nlinarith [congrArg (fun a : ℝ => μ * a) h1]
  have hnμ : μ ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg μ]
  have hv1 : v 1 = 0 := (mul_eq_zero.mp hp).resolve_left hnμ
  apply hn
  ext i
  fin_cases i <;> simp_all

theorem rotation_real_not_diagonalizable :
    Specs.D05.M09.FieldDependence.rotation_real_not_diagonalizable := by
  rintro ⟨n, b, μ, hb⟩
  have he (i : Fin n) : (rotation ℝ).HasEigenvalue (μ i) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hb i), b.ne_zero i⟩)
  have hempty : IsEmpty (Fin n) := ⟨fun i => rotation_real_no_eigenvalues (μ i) (he i)⟩
  let _ := hempty
  have hsub := b.repr.injective
  have hz : (firstVector ℝ) = 0 := hsub (Subsingleton.elim _ _)
  have := congrFun hz 0
  simp [firstVector] at this

theorem rotation_complex_eigenvectors :
    Specs.D05.M09.FieldDependence.rotation_complex_eigenvectors := by
  intro j
  apply Module.End.hasEigenvector_iff.mpr
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    rw [rotation_apply]
    ext i
    fin_cases j <;> fin_cases i <;>
      simp [complexVectors, complexEigenvalues]
  · intro h
    have h0 := congrFun h 0
    fin_cases j <;> simp [complexVectors] at h0

theorem rotation_complex_independent :
    Specs.D05.M09.FieldDependence.rotation_complex_independent := by
  unfold Specs.D05.M09.FieldDependence.rotation_complex_independent
  rw [linearIndependent_fin2]
  constructor
  · exact (rotation_complex_eigenvectors 1).2
  · intro a h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [complexVectors] at h0 h1
    subst a
    have hi := congrArg Complex.im h1
    norm_num at hi

theorem rotation_complex_eigenbasis :
    Specs.D05.M09.FieldDependence.rotation_complex_eigenbasis := by
  classical
  let b := basisOfPiSpaceOfLinearIndependent rotation_complex_independent
  have hb (j : Fin 2) : b j = complexVectors j := by
    exact congrFun (coe_basisOfPiSpaceOfLinearIndependent rotation_complex_independent) j
  refine ⟨b, hb, ?_⟩
  apply (D05.M09.Diagonalizable.matrix_eq_diagonal_iff b (rotation ℂ)
    complexEigenvalues).mpr
  intro j
  rw [hb]
  exact Module.End.mem_eigenspace_iff.mp (rotation_complex_eigenvectors j).1

theorem rotation_complex_diagonalizable :
    Specs.D05.M09.FieldDependence.rotation_complex_diagonalizable := by
  obtain ⟨b, hb, _⟩ := rotation_complex_eigenbasis
  refine ⟨2, b, complexEigenvalues, ?_⟩
  intro j
  rw [hb]
  exact Module.End.mem_eigenspace_iff.mp (rotation_complex_eigenvectors j).1

theorem jordan_charpoly : Specs.D05.M09.FieldDependence.jordan_charpoly := by
  intro K _
  rw [jordan, Matrix.charpoly_mulVecLin, Matrix.charpoly_fin_two]
  simp [jordanMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- Solving the two coordinate equations gives the entire eigenspace at one. -/
theorem jordan_eigenspace_one : Specs.D05.M09.FieldDependence.jordan_eigenspace_one := by
  intro K _
  constructor
  · simpa only [one_smul, Module.End.one_eq_id] using
      (Module.End.eigenspace_def (f := jordan K) (μ := (1 : K)))
  · ext v
    rw [Module.End.mem_eigenspace_iff, jordan_apply, Submodule.mem_span_singleton]
    constructor
    · intro h
      have h0 := congrFun h 0
      have hv1 : v 1 = 0 := by simpa using h0
      refine ⟨v 0, ?_⟩
      ext i
      fin_cases i <;> simp [firstVector, hv1]
    · rintro ⟨a, rfl⟩
      ext i
      fin_cases i <;> simp [firstVector]

/-- Away from one, both coordinates vanish. No closure assumption is needed. -/
theorem jordan_other_eigenspaces :
    Specs.D05.M09.FieldDependence.jordan_other_eigenspaces := by
  intro K _ μ hμ
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have he := Module.End.mem_eigenspace_iff.mp hv
  rw [jordan_apply] at he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  change v 0 + v 1 = μ * v 0 at h0
  change v 1 = μ * v 1 at h1
  have hn : (1 : K) - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  have hp1 : (1 - μ) * v 1 = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
  have hv1 : v 1 = 0 := (mul_eq_zero.mp hp1).resolve_left hn
  have hp0 : (1 - μ) * v 0 = 0 := by
    rw [hv1, add_zero] at h0
    rw [sub_mul, one_mul, ← h0, sub_self]
  have hv0 : v 0 = 0 := (mul_eq_zero.mp hp0).resolve_left hn
  ext i
  fin_cases i <;> simp [hv0, hv1]

theorem jordan_eigenvalue_iff : Specs.D05.M09.FieldDependence.jordan_eigenvalue_iff := by
  intro K _ μ
  constructor
  · intro h
    by_contra hμ
    exact h (jordan_other_eigenspaces K μ hμ)
  · rintro rfl
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := firstVector K)
    apply Module.End.hasEigenvector_iff.mpr
    constructor
    · rw [(jordan_eigenspace_one K).2]
      exact Submodule.subset_span (Set.mem_singleton _)
    · intro hz
      have h0 := congrFun hz 0
      simp [firstVector] at h0

theorem jordan_eigenspace_dimension :
    Specs.D05.M09.FieldDependence.jordan_eigenspace_dimension := by
  intro K _
  rw [(jordan_eigenspace_one K).2]
  apply finrank_span_singleton
  intro hz
  have h0 := congrFun hz 0
  simp [firstVector] at h0

/-- An eigenbasis would make J fix every basis vector and therefore equal I₂. -/
theorem jordan_not_diagonalizable :
    Specs.D05.M09.FieldDependence.jordan_not_diagonalizable := by
  intro K _
  rintro ⟨n, b, μ, hb⟩
  have hμ (i : Fin n) : μ i = 1 := by
    apply (jordan_eigenvalue_iff K (μ i)).mp
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := b i)
    exact Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (hb i), b.ne_zero i⟩
  have heq : jordan K = (LinearMap.id : Module.End K (Fin 2 → K)) := by
    apply b.ext
    intro i
    simpa [hμ i] using hb i
  have hv := LinearMap.congr_fun heq (![0, 1] : Fin 2 → K)
  rw [jordan_apply] at hv
  have h0 := congrFun hv 0
  simp at h0

theorem identity_charpoly : Specs.D05.M09.FieldDependence.identity_charpoly := by
  intro K _
  simpa [Module.End.one_eq_id] using (LinearMap.charpoly_one (R := K) (M := Fin 2 → K))

theorem identity_diagonal_matrix :
    Specs.D05.M09.FieldDependence.identity_diagonal_matrix := by
  intro K _
  simp

theorem identity_diagonalizable :
    Specs.D05.M09.FieldDependence.identity_diagonalizable := by
  intro K _
  exact ⟨2, Pi.basisFun K (Fin 2), (fun _ => 1), fun _ => by simp⟩

theorem same_charpoly_different_diagonalizability :
    Specs.D05.M09.FieldDependence.same_charpoly_different_diagonalizability := by
  exact ⟨(jordan_charpoly ℂ).trans (identity_charpoly ℂ).symm,
    jordan_not_diagonalizable ℂ, identity_diagonalizable ℂ⟩

end D05.M09.FieldDependence
