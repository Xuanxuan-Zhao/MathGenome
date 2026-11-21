import MathGenome.Internal.Specs.D05.M15.PolynomialBridge
import MathGenome.Internal.D05.M07.DualBasis
import MathGenome.Internal.D05.M15.SymmetricBasis
import MathGenome.Internal.D05.Foundations.RootBound
import MathGenome.Internal.D05.M15.PolynomialBridge.Domain
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic

noncomputable section
namespace D05.M15.PolynomialBridge
open D05.Foundations
open Specs.D05.M15.Symmetric
universe u v

abbrev evaluation := Specs.D05.M15.PolynomialBridge.evaluation
abbrev coordinateEvaluation := @Specs.D05.M15.PolynomialBridge.coordinateEvaluation
abbrev dualPolynomialEquiv := @Specs.D05.M15.PolynomialBridge.dualPolynomialEquiv

theorem evaluation_generator :
    Specs.D05.M15.PolynomialBridge.evaluation_generator.{u,v} := by
  intro K V _ _ _ f v
  exact congrFun (_root_.SymmetricAlgebra.lift_ι_apply _ f) v

theorem coordinate_evaluation_apply :
    Specs.D05.M15.PolynomialBridge.coordinate_evaluation_apply.{u,v} := by
  intro K V _ _ _ n b p v
  change (Pi.evalAlgHom K (fun _ : V => K) v)
    (MvPolynomial.aeval (fun i v => b.coord i v) p) = _
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem polynomial_coordinates :
    Specs.D05.M15.PolynomialBridge.polynomial_coordinates.{u,v} := by
  intro K V _ _ _ n b i
  simpa only [dualPolynomialEquiv, Specs.D05.M15.PolynomialBridge.dualPolynomialEquiv,
    congrFun b.coe_dualBasis i] using D05.M15.SymmetricBasis.polynomial_generators b.dualBasis i

theorem evaluation_bridge :
    Specs.D05.M15.PolynomialBridge.evaluation_bridge.{u,v} := by
  intro K V _ _ _ n b
  apply _root_.SymmetricAlgebra.algHom_ext
  apply b.dualBasis.ext
  intro i
  ext v
  change evaluation K V (_root_.SymmetricAlgebra.ι K _ (b.dualBasis i)) v =
    coordinateEvaluation b (dualPolynomialEquiv b (_root_.SymmetricAlgebra.ι K _
      (b.dualBasis i))) v
  rw [congrFun b.coe_dualBasis i, (polynomial_coordinates b i).1]
  simpa [coordinateEvaluation, Specs.D05.M15.PolynomialBridge.coordinateEvaluation]
    using evaluation_generator (b.coord i) v

theorem formal_evaluation_injective :
    Specs.D05.M15.PolynomialBridge.formal_evaluation_injective.{u} := by
  intro K _ _ n p q h
  exact MvPolynomial.funext (congrFun h)

theorem coordinate_evaluation_injective :
    Specs.D05.M15.PolynomialBridge.coordinate_evaluation_injective.{u,v} := by
  intro K V _ _ _ _ n b p q h
  apply formal_evaluation_injective K n
  funext a
  have hv := congrFun h (∑ i, a i • b i)
  change coordinateEvaluation b p _ = coordinateEvaluation b q _ at hv
  rw [coordinate_evaluation_apply, coordinate_evaluation_apply] at hv
  simpa only [Module.Basis.coord_apply, Module.Basis.repr_sum_self] using hv

theorem evaluation_injective :
    Specs.D05.M15.PolynomialBridge.evaluation_injective.{u,v} := by
  intro K V _ _ _ _ n b p q h
  apply (dualPolynomialEquiv b).injective
  apply coordinate_evaluation_injective b
  rw [evaluation_bridge b] at h
  exact h

theorem zero_variables_injective :
    Specs.D05.M15.PolynomialBridge.zero_variables_injective.{u,v} := by
  intro K V _ _ _ b
  have hc : Function.Injective (coordinateEvaluation b) := by
    intro p q h
    have hv := congrFun h (0 : V)
    rw [coordinate_evaluation_apply, coordinate_evaluation_apply,
      MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eq_C_of_isEmpty q] at hv
    have he : p.coeff 0 = q.coeff 0 := by simpa using hv
    rw [MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eq_C_of_isEmpty q, he]
  refine ⟨hc, ?_⟩
  intro p q h
  apply (dualPolynomialEquiv b).injective
  apply hc
  rw [evaluation_bridge b] at h
  exact h

/-- A single variable remains a genuine formal variable, independently of
how many scalar values the field has. -/
theorem variable_frobenius_ne_zero {K : Type u} [Field K] [Fintype K]
    {n : ℕ} (i : Fin n) :
    (MvPolynomial.X i ^ Fintype.card K - MvPolynomial.X i : FormalPolynomial K n) ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.aeval (fun _ : Fin n => Polynomial.X :
      Fin n → Polynomial K)) h
  have hn := FiniteField.X_pow_card_sub_X_ne_zero K (Fintype.one_lt_card (α := K))
  apply hn
  simpa using he

theorem finite_field_counterexample :
    Specs.D05.M15.PolynomialBridge.finite_field_counterexample.{u} := by
  intro K _ _
  refine ⟨variable_frobenius_ne_zero (0 : Fin 1), ?_⟩
  intro a
  simp [FiniteField.pow_card]

theorem finite_field_symmetric_counterexample :
    Specs.D05.M15.PolynomialBridge.finite_field_symmetric_counterexample.{u,v} := by
  intro K V _ _ _ _ n b i
  dsimp only
  constructor
  · intro h
    have he := congrArg (dualPolynomialEquiv b) h
    simp only [map_sub, map_pow, map_zero, (polynomial_coordinates b i).1] at he
    exact variable_frobenius_ne_zero i he
  · ext v
    simp [FiniteField.pow_card]

theorem formal_polynomial_domain :
    Specs.D05.M15.PolynomialBridge.formal_polynomial_domain.{u} :=
  Domain.formal_polynomial_domain

theorem symmetric_domain :
    Specs.D05.M15.PolynomialBridge.symmetric_domain.{u,v} :=
  Domain.symmetric_domain

end D05.M15.PolynomialBridge
