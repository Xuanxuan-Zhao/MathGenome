import MathGenome.Internal.Specs.D05.Foundations.Division
import MathGenome.Internal.D05.Foundations.FormalPolynomials
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Division with a jointly unique quotient and remainder, including a zero
dividend and a nonzero constant divisor. -/

namespace D05.Foundations.Division

/-- The field polynomial division algorithm of paper.tex:361–367. -/
theorem divisionAlgorithm : D05.Specs.Division.divisionAlgorithm := by
  intro K _ a b hb
  refine ⟨(a / b, a % b), ⟨(EuclideanDomain.div_add_mod' a b).symm, ?_⟩, ?_⟩
  · by_cases hr : a % b = 0
    · exact Or.inl hr
    · exact Or.inr (Polynomial.natDegree_lt_natDegree hr (Polynomial.degree_mod_lt a hb))
  · rintro ⟨q, r⟩ ⟨heq, hr⟩
    change r = 0 ∨ r.natDegree < b.natDegree at hr
    have hrmod : r % b = r := by
      rcases hr with hr | hr
      · simp [hr]
      · exact (Polynomial.mod_eq_self_iff hb).2 (Polynomial.degree_lt_degree hr)
    have hrem : a % b = r := by
      calc
        a % b = r % b := Polynomial.mod_eq_of_dvd_sub ⟨q, by
          rw [heq, add_sub_cancel_right, mul_comm]⟩
        _ = r := hrmod
    apply Prod.ext
    · apply mul_right_cancel₀ hb
      apply add_right_cancel (b := r)
      calc
        q * b + r = a := heq.symm
        _ = a / b * b + r := by
          rw [← hrem]
          exact (EuclideanDomain.div_add_mod' a b).symm
    · exact hrem.symm

end D05.Foundations.Division
