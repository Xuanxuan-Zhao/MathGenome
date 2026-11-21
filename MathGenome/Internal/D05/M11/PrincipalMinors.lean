import MathGenome.Internal.Specs.D05.M11.PrincipalMinors
import MathGenome.Internal.D05.M11.PrincipalMinors.Leading
import MathGenome.Internal.D05.M11.PrincipalMinors.Semidefinite
import MathGenome.Internal.D05.M11.Hermitian

/-! K05.11.principal_minors: assembly of the strict and semidefinite tests.
The proof stages establish Schur reduction and the inertia/perturbation argument;
the final criteria below have only the original symmetry hypotheses. -/
noncomputable section
open Matrix

namespace D05.M11.PrincipalMinors

theorem complex_criteria : Specs.D05.M11.PrincipalMinors.complex_criteria := by
  intro n A hA
  exact ⟨Leading.strict_criterion A hA, Semidefinite.criterion A hA⟩

theorem real_criteria : Specs.D05.M11.PrincipalMinors.real_criteria := by
  intro n A hA
  exact ⟨Leading.real_strict_criterion A hA, Semidefinite.real_criterion A hA⟩

theorem form_strict_criterion : Specs.D05.M11.PrincipalMinors.form_strict_criterion :=
  Leading.form_criterion

theorem form_complex_semidefinite_criterion :
    Specs.D05.M11.PrincipalMinors.form_complex_semidefinite_criterion :=
  Semidefinite.form_criterion

theorem form_real_semidefinite_criterion :
    Specs.D05.M11.PrincipalMinors.form_real_semidefinite_criterion := by
  intro V _ _ n e B hB
  let H := Specs.D05.M11.Hermitian.formMatrix_value e B
  have hH : H.IsHermitian := (D05.M11.Hermitian.hermitian_iff_matrix e B).mp hB
  have hq (v : V) : B v v = star (e.equivFun v) ⬝ᵥ Hᵀ *ᵥ e.equivFun v :=
    D05.M11.Hermitian.quadratic_matrix_expression e B v
  have hb : Specs.D05.M11.Definiteness.positiveSemidefinite_value (fun x y => B x y) ↔
      ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ Hᵀ *ᵥ x := by
    constructor
    · intro h x
      have hh := h (e.equivFun.symm x)
      change 0 ≤ B _ _ at hh
      rw [hq] at hh
      simpa only [LinearEquiv.apply_symm_apply, star_trivial] using hh
    · intro h v
      change 0 ≤ B v v
      rw [hq]
      simpa only [star_trivial] using h (e.equivFun v)
  exact hb.trans ((Semidefinite.real_criterion Hᵀ hH.transpose.isSymm).trans
    (Semidefinite.transpose_criterion H))

theorem transpose_criteria : Specs.D05.M11.PrincipalMinors.transpose_criteria := by
  intro K _ n H
  refine ⟨fun s => Leading.principal_transpose H s, ?_,
    Semidefinite.transpose_criterion H⟩
  unfold Specs.D05.M11.PrincipalMinors.Leading.LeadingPositive
    Specs.D05.M11.PrincipalMinors.Leading.leadingBlock
  simp only [← transpose_submatrix, det_transpose]

theorem leading_minors_insufficient :
    Specs.D05.M11.PrincipalMinors.leading_minors_insufficient := by
  refine ⟨?_, Semidefinite.leading_minors_insufficient⟩
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem empty_case : Specs.D05.M11.PrincipalMinors.empty_case := by
  intro K _ A
  obtain ⟨hp, hl⟩ := Leading.empty_positive_definite A
  refine ⟨hp, hl, ?_, ?_⟩
  · intro x
    simp [dotProduct]
  · intro s
    simp

theorem empty_minor : Specs.D05.M11.PrincipalMinors.empty_minor :=
  Semidefinite.empty_minor

end D05.M11.PrincipalMinors
