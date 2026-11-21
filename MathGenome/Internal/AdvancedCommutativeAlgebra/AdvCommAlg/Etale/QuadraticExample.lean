import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.QuadraticExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.SquareJacobianCriterion
import Mathlib.Algebra.MvPolynomial.Equiv

namespace AdvCommAlg.Etale

universe u
noncomputable section

open Specs.AdvCommAlg.Etale
open Specs.AdvCommAlg.Differentials

theorem quadratic_root_relation : quadraticRootRelation.{u} := by
  intro A _ a
  let I : Ideal (Polynomial A) := Ideal.span {Polynomial.X ^ 2 - Polynomial.C a}
  have h : Ideal.Quotient.mk I (Polynomial.X ^ 2 - Polynomial.C a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  change (Ideal.Quotient.mk I Polynomial.X) ^ 2 =
    algebraMap A (Polynomial A ⧸ I) a
  rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_eq]
  exact sub_eq_zero.mp (by simpa only [map_sub, map_pow] using h)

theorem quadratic_derivative_unit : quadraticDerivativeUnit.{u} := by
  intro A _ a htwo ha
  have hx2 : IsUnit ((Ideal.Quotient.mk
      (Ideal.span {Polynomial.X ^ 2 - Polynomial.C a}) Polynomial.X) ^ 2) := by
    rw [quadratic_root_relation A a]
    exact ha.map (algebraMap A (QuadraticQuotient A a))
  have hx : IsUnit (Ideal.Quotient.mk
      (Ideal.span {Polynomial.X ^ 2 - Polynomial.C a}) Polynomial.X) := by
    exact isUnit_of_mul_isUnit_left (by simpa only [pow_two] using hx2)
  have htwo' : IsUnit (2 : QuadraticQuotient A a) := by
    simpa only [map_ofNat] using htwo.map (algebraMap A (QuadraticQuotient A a))
  simpa [Polynomial.derivative_pow, map_ofNat] using htwo'.mul hx

private def quadraticRelations {A : Type u} [CommRing A] (a : A) :
    Fin 1 → MvPolynomial (Fin 1) A :=
  fun _ => MvPolynomial.X 0 ^ 2 - MvPolynomial.C a

private def quadraticQuotientEquiv {A : Type u} [CommRing A] (a : A) :
    JacobianQuotient A 1 1 (quadraticRelations a) ≃ₐ[A] QuadraticQuotient A a :=
  Ideal.quotientEquivAlg (Ideal.span (Set.range (quadraticRelations a)))
    (Ideal.span {Polynomial.X ^ 2 - Polynomial.C a})
    (MvPolynomial.uniqueAlgEquiv A (Fin 1)) (by
      rw [Ideal.map_span]
      change Ideal.span {Polynomial.X ^ 2 - Polynomial.C a} =
        Ideal.span ((MvPolynomial.uniqueAlgEquiv A (Fin 1)) ''
          Set.range (fun _ : Fin 1 => MvPolynomial.X 0 ^ 2 - MvPolynomial.C a))
      simp [Set.range_const, MvPolynomial.uniqueAlgEquiv])

theorem quadratic_etale : quadraticEtale.{u} := by
  intro A _ a htwo ha
  apply (square_jacobian_criterion A (QuadraticQuotient A a)).mpr
  refine ⟨1, quadraticRelations a, (quadraticQuotientEquiv a).symm, ?_⟩
  have h := quadratic_derivative_unit A a htwo ha
  simpa [quotientJacobianMatrix, quadraticRelations, Matrix.det_fin_one,
    MvPolynomial.pderiv_pow, quadraticQuotientEquiv, MvPolynomial.uniqueAlgEquiv,
    Polynomial.derivative_sub, Polynomial.derivative_pow, map_ofNat] using h

end
end AdvCommAlg.Etale
