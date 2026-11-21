import MathGenome.Internal.D05.M03.MapAlgebra
import MathGenome.Internal.D05.Foundations.FormalPolynomials
import MathGenome.Internal.Specs.D05.M08.Evaluation

/-! Polynomial evaluation in the canonical endomorphism algebra.
The codomain is allowed to be noncommutative and to be the zero algebra.
All statements are valid without a finite-dimensional hypothesis.
-/

noncomputable section

namespace D05.M08.Evaluation

open scoped BigOperators

/-- The unital K-algebra homomorphism evaluating a formal polynomial at T. -/
def evaluation (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) : Polynomial K →ₐ[K] Module.End K V :=
  Polynomial.aeval T

theorem coefficient_sum : Specs.D05.M08.Evaluation.coefficient_sum := by
  intro K V _ _ _ T p
  exact Polynomial.aeval_eq_sum_range T

theorem coefficient_sum_of_bound : Specs.D05.M08.Evaluation.coefficient_sum_of_bound := by
  intro K V _ _ _ T p d hd
  exact Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd) T

theorem finite_expansion : Specs.D05.M08.Evaluation.finite_expansion := by
  intro K V _ _ _ T s a
  change Polynomial.aeval T _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.aeval_monomial, Algebra.smul_def]

theorem zero_padding : Specs.D05.M08.Evaluation.zero_padding := by
  intro K V _ _ _ T p d e hd he
  exact (coefficient_sum_of_bound T p d hd).symm.trans
    (coefficient_sum_of_bound T p e (hd.trans he))

theorem eval_zero : Specs.D05.M08.Evaluation.eval_zero := by
  intro K V _ _ _ T
  exact map_zero (Polynomial.aeval T)

theorem eval_add : Specs.D05.M08.Evaluation.eval_add := by
  intro K V _ _ _ T p q
  exact map_add (Polynomial.aeval T) p q

theorem eval_smul : Specs.D05.M08.Evaluation.eval_smul := by
  intro K V _ _ _ T a p
  exact map_smul (Polynomial.aeval T) a p

theorem eval_mul : Specs.D05.M08.Evaluation.eval_mul := by
  intro K V _ _ _ T p q
  exact map_mul (Polynomial.aeval T) p q

theorem eval_one : Specs.D05.M08.Evaluation.eval_one := by
  intro K V _ _ _ T
  exact map_one (Polynomial.aeval T)

theorem eval_constant : Specs.D05.M08.Evaluation.eval_constant := by
  intro K V _ _ _ T a
  exact Polynomial.aeval_C T a

theorem eval_variable : Specs.D05.M08.Evaluation.eval_variable := by
  intro K V _ _ _ T
  exact Polynomial.aeval_X T

theorem eval_powers : Specs.D05.M08.Evaluation.eval_powers := by
  intro K V _ _ _ T j
  exact ⟨Polynomial.aeval_X_pow T, pow_zero T⟩

theorem polynomials_commute : Specs.D05.M08.Evaluation.polynomials_commute := by
  intro K V _ _ _ T p q
  calc
    _ = Polynomial.aeval T (p * q) := (map_mul (Polynomial.aeval T) p q).symm
    _ = Polynomial.aeval T (q * p) := congrArg (Polynomial.aeval T) (mul_comm p q)
    _ = _ := map_mul (Polynomial.aeval T) q p

theorem product_convolution : Specs.D05.M08.Evaluation.product_convolution := by
  intro K V _ _ _ T p q
  rw [← coefficient_sum T p, ← coefficient_sum T q, ← eval_mul T p q,
    coefficient_sum T (p * q)]
  simp only [Polynomial.coeff_mul]

theorem eval_apply : Specs.D05.M08.Evaluation.eval_apply := by
  intro K V _ _ _ T p v
  rw [coefficient_sum T p]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]

theorem zero_space : Specs.D05.M08.Evaluation.zero_space := by
  intro K V _ _ _ _ T p
  constructor <;> ext v <;> exact Subsingleton.elim _ _

end D05.M08.Evaluation
