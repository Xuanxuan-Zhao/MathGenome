import MathGenome.Internal.Specs.D05.M05.DetDefinition
import MathGenome.Internal.D05.Foundations.PermutationSign

/-! K05.05.det_definition: the column Leibniz determinant over commutative rings. -/

noncomputable section

namespace D05.M05.DetDefinition

open scoped BigOperators
open D05.Foundations

def determinant : D05.Specs.DetDefinition.determinant_type :=
  D05.Specs.DetDefinition.determinant_value

theorem leibniz_formula : D05.Specs.DetDefinition.leibniz_formula := by
  intro R _ n A
  rfl

theorem matrix_det_bridge : D05.Specs.DetDefinition.matrix_det_bridge := by
  intro R _ n A
  unfold D05.M05.determinant
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rw [D05.Foundations.PermutationSign.signIdentification]

theorem empty_expansion : D05.Specs.DetDefinition.empty_expansion := by
  constructor
  · intro σ
    exact ⟨Subsingleton.elim _ _, (D05.Foundations.PermutationSign.emptyCase.{0}.1 σ).2⟩
  · intro R _ A σ
    simp

theorem empty_determinant : D05.Specs.DetDefinition.empty_determinant := by
  intro R _ A
  rw [matrix_det_bridge]
  exact Matrix.det_isEmpty

theorem identity_summand : D05.Specs.DetDefinition.identity_summand := by
  intro R _ n σ
  classical
  by_cases hσ : σ = 1
  · subst σ
    rw [D05.Foundations.PermutationSign.signIdentification]
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul]
    change (∏ j : Fin n, (1 : Matrix (Fin n) (Fin n) R) j j) = 1
    simp
  · rw [ite_eq_right hσ]
    obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
      by_contra h
      push Not at h
      exact hσ (Equiv.ext h)
    have hp : (∏ j, (1 : Matrix (Fin n) (Fin n) R) (σ j) j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj]
    rw [hp, mul_zero]

theorem identity_determinant : D05.Specs.DetDefinition.identity_determinant := by
  intro R _ n
  rw [matrix_det_bridge]
  exact Matrix.det_one

theorem column_add : D05.Specs.DetDefinition.column_add := by
  intro R _ n A j u v
  rw [matrix_det_bridge, matrix_det_bridge, matrix_det_bridge]
  exact Matrix.det_updateCol_add A j u v

theorem column_smul : D05.Specs.DetDefinition.column_smul := by
  intro R _ n A j a u
  rw [matrix_det_bridge, matrix_det_bridge]
  exact Matrix.det_updateCol_smul A j a u

theorem pairing_involution : D05.Specs.DetDefinition.pairing_involution := by
  intro n j k hjk σ
  constructor
  · exact Equiv.mul_swap_involutive j k σ
  · intro h
    have hs : Equiv.swap j k = (1 : Equiv.Perm (Fin n)) := by
      apply mul_left_cancel (a := σ)
      simpa using h
    have he := Equiv.congr_fun hs j
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at he
    exact hjk he.symm

theorem paired_summands : D05.Specs.DetDefinition.paired_summands := by
  intro R _ n A j k hjk hcol σ
  have hp : (∏ l, A ((σ * Equiv.swap j k) l) l) = (∏ l, A (σ l) l) := by
    rw [← Equiv.prod_comp (Equiv.swap j k) (fun l => A (σ l) l)]
    apply Finset.prod_congr rfl
    intro l _
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    exact (Equiv.apply_swap_eq_self (hcol (σ (Equiv.swap j k l))) l).symm
  refine ⟨hp, ?_⟩
  rw [hp, D05.Foundations.PermutationSign.signMultiplicative,
    D05.Foundations.PermutationSign.signTransposition n j k hjk]
  simp

theorem equal_columns_zero : D05.Specs.DetDefinition.equal_columns_zero := by
  intro R _ n A j k hjk hcol
  rw [leibniz_formula]
  exact Finset.sum_involution (fun σ _ => σ * Equiv.swap j k)
    (fun σ _ => by rw [(paired_summands A j k hjk hcol σ).2, add_neg_cancel])
    (fun σ _ _ => (pairing_involution n j k hjk σ).2)
    (fun σ _ => Finset.mem_univ _)
    (fun σ _ => (pairing_involution n j k hjk σ).1)

theorem normalized_column_form : D05.Specs.DetDefinition.normalized_column_form := by
  intro R _ n
  refine ⟨Matrix.detRowAlternating, ?_, ?_⟩
  · intro v
    change Matrix.det (Matrix.of v) = D05.M05.determinant (Matrix.transpose (Matrix.of v))
    rw [matrix_det_bridge, Matrix.det_transpose]
  · change Matrix.det (Matrix.transpose (1 : Matrix (Fin n) (Fin n) R)) = 1
    rw [Matrix.transpose_one, Matrix.det_one]

end D05.M05.DetDefinition
