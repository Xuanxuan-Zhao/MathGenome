import MathGenome.Internal.Specs.D07.Ch11.PolynomialFunction
import MathGenome.Internal.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.D07.Ch11.RootBound
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
K07.11.polynomial_function. The finite-field argument uses just multiplication
on the finite set of nonzero elements and cancellation of their product.
The infinite-domain argument uses the upstream finiteness of the roots of
a nonzero polynomial, applied to the difference. No finite-field
classification, cyclicity, or characteristic theorem is used.
-/

universe u

namespace D07.Ch11.PolynomialFunction

open Polynomial
open Specs.D07.Ch11.PolynomialFunction

theorem nonzero_multiplication_permutation : NonzeroMultiplicationPermutation.{u} := by
  intro F _ a ha
  constructor
  · intro b c h
    apply Subtype.ext
    exact mul_left_cancel₀ ha (congrArg Subtype.val h)
  · intro b
    refine ⟨⟨a⁻¹ * b.val, mul_ne_zero (inv_ne_zero ha) b.property⟩, ?_⟩
    apply Subtype.ext
    change a * (a⁻¹ * b.val) = b.val
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

theorem nonzero_product_comparison : NonzeroProductComparison.{u} := by
  intro F _ _
  classical
  have hc : Fintype.card {x : F // x ≠ 0} = Fintype.card F - 1 := by
    simp
  refine ⟨hc, ?_⟩
  dsimp only
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun b _ => b.property), ?_⟩
  intro a ha
  have hperm := (nonzero_multiplication_permutation F a ha).prod_comp
    (fun b : {x : F // x ≠ 0} => b.val)
  calc
    (∏ b : {x : F // x ≠ 0}, b.val) =
        ∏ b : {x : F // x ≠ 0}, a * b.val := hperm.symm
    _ = a ^ (Fintype.card F - 1) * ∏ b : {x : F // x ≠ 0}, b.val := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, hc]

theorem nonzero_power_identity : NonzeroPowerIdentity.{u} := by
  intro F _ _ a ha
  classical
  obtain ⟨_, hP, hcompare⟩ := nonzero_product_comparison F
  exact mul_right_cancel₀ hP ((hcompare a ha).symm.trans (one_mul _).symm)

theorem finite_power_identity : FinitePowerIdentity.{u} := by
  intro F _ _ a
  apply sub_eq_zero.mpr
  by_cases ha : a = 0
  · simp [ha, Fintype.card_ne_zero]
  · calc
      a ^ Fintype.card F = a ^ ((Fintype.card F - 1) + 1) := by
        rw [Nat.sub_add_cancel Fintype.card_pos]
      _ = a := by rw [pow_succ, nonzero_power_identity F a ha, one_mul]

theorem finite_cardinality : FiniteCardinality.{u} := by
  intro F _ _
  exact Fintype.one_lt_card

theorem witness_coefficients : WitnessCoefficients.{u} := by
  intro F _ _
  have hq : Fintype.card F ≠ 1 := ne_of_gt (finite_cardinality F)
  constructor
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_X,
      Ne.symm hq, ite_false, sub_zero]
  · simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Ne.symm hq]

theorem witness_nonzero : WitnessNonzero.{u} := by
  intro F _ _ h
  have hcoeff := (witness_coefficients F).1
  rw [h, Polynomial.coeff_zero] at hcoeff
  exact zero_ne_one hcoeff

theorem witness_vanishes : WitnessVanishes.{u} := by
  intro F _ _ a
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] using
    finite_power_identity F a

theorem finite_evaluation_noninjective : FiniteEvaluationNoninjective.{u} := by
  intro F _ _ hinj
  apply witness_nonzero F
  apply hinj
  funext a
  change (X ^ Fintype.card F - X : Polynomial F).eval a = (0 : Polynomial F).eval a
  rw [witness_vanishes F a, Polynomial.eval_zero]

theorem infinite_evaluation_injective : InfiniteEvaluationInjective.{u} := by
  intro R _ _ _ f g hfg
  apply sub_eq_zero.mp
  by_contra hne
  have hroots := D07.Ch11.RootBound.roots_finite R (f - g) hne
  have hz : ∀ a : R, (f - g).eval a = 0 := by
    intro a
    rw [Polynomial.eval_sub, sub_eq_zero]
    exact congrFun hfg a
  have hset : {a : R | (f - g).eval a = 0} = Set.univ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hz a
  rw [hset] at hroots
  exact Set.infinite_univ hroots

theorem infinite_evaluation_equality : InfiniteEvaluationEquality.{u} := by
  intro R _ _ _ f g
  constructor
  · intro h
    exact infinite_evaluation_injective R (funext h)
  · rintro rfl a
    rfl

end D07.Ch11.PolynomialFunction
