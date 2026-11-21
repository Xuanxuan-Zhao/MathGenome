import MathGenome.Internal.Specs.D07.Ch09.MaximalPrimeNonconverse
import MathGenome.Internal.D07.Ch09.MaximalQuotient
import MathGenome.Internal.D07.Ch09.PrimeQuotient
import MathGenome.Internal.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.D07.Ch11.PolynomialDefinition
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Ring.Int.Field
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.NormNum

/-!
K07.09.maximal_prime_nonconverse. The quotient criteria give the general
implication. Evaluation at zero identifies the quotient by (X) with ℤ.
The shifted coefficients supply the kernel calculation directly, and
constant coefficients distinguish the two steps of the strict ideal chain.
-/

universe u

namespace D07.Ch09.MaximalPrimeNonconverse

open Polynomial
open Specs.D07.Ch09.MaximalPrimeNonconverse

theorem field_implies_domain : FieldImpliesDomain.{u} := by
  intro R _ h
  exact h.isDomain

theorem maximal_implies_prime : MaximalImpliesPrime.{u} := by
  intro R _ M hM
  apply (PrimeQuotient.prime_iff_quotient_domain R M).mpr
  exact field_implies_domain _ ((MaximalQuotient.maximal_iff_isField_quotient R M).mp hM)

theorem integer_domain_not_field : IntegerDomainNotField :=
  ⟨inferInstance, Int.not_isField⟩

theorem integer_zero_prime_not_maximal : IntegerZeroPrimeNotMaximal := by
  refine ⟨(PrimeQuotient.domain_iff_bot_prime ℤ).mp integer_domain_not_field.1, ?_⟩
  intro h
  have hf := (MaximalQuotient.maximal_iff_isField_quotient ℤ ⊥).mp h
  exact integer_domain_not_field.2 ((RingEquiv.quotientBot ℤ).symm.toMulEquiv.isField hf)

theorem shifted_decomposition : ShiftedDecomposition := by
  intro f
  refine ⟨f.divX, fun n => coeff_divX, ?_⟩
  rw [← coeff_zero_eq_eval_zero]
  exact (X_mul_divX_add f).symm.trans (add_comm _ _)

theorem evaluation_zero_iff_multiple : EvaluationZeroIffMultiple := by
  intro f
  constructor
  · intro hf
    obtain ⟨g, _, hg⟩ := shifted_decomposition f
    exact ⟨g, by simpa [hf] using hg⟩
  · rintro ⟨g, rfl⟩
    simp

theorem evaluation_surjective : EvaluationSurjective := by
  intro a
  exact ⟨C a, eval_C⟩

theorem evaluation_kernel : EvaluationKernel := by
  ext f
  change f.eval 0 = 0 ↔ f ∈ Ideal.span ({X} : Set (Polynomial ℤ))
  rw [Ideal.mem_span_singleton, evaluation_zero_iff_multiple]

theorem quotient_equivalence : QuotientEquivalence := by
  let e₁ := Ideal.quotEquivOfEq evaluation_kernel.symm
  let e₂ := (evalRingHom (0 : ℤ)).quotientKerEquivOfSurjective evaluation_surjective
  refine ⟨e₁.trans e₂, ?_⟩
  intro f
  change e₂ (Ideal.Quotient.mk _ f) = f.eval 0
  exact RingHom.quotientKerEquivOfSurjective_apply_mk evaluation_surjective f

theorem quotient_domain_not_field : QuotientDomainNotField := by
  obtain ⟨e, _⟩ := quotient_equivalence
  exact ⟨e.toMulEquiv.isDomain_iff.mpr integer_domain_not_field.1,
    fun h => integer_domain_not_field.2 (e.symm.toMulEquiv.isField h)⟩

theorem x_ideal_nonzero_prime_not_maximal : XIdealNonzeroPrimeNotMaximal := by
  refine ⟨?_, (PrimeQuotient.prime_iff_quotient_domain _ _).mpr
    quotient_domain_not_field.1, ?_⟩
  · intro h
    have hx : (X : Polynomial ℤ) ∈ Ideal.span ({X} : Set (Polynomial ℤ)) :=
      Ideal.subset_span (Set.mem_singleton X)
    rw [h, Ideal.mem_bot] at hx
    exact X_ne_zero hx
  · intro h
    exact quotient_domain_not_field.2
      ((MaximalQuotient.maximal_iff_isField_quotient _ _).mp h)

theorem two_x_representation : TwoXRepresentation := by
  intro f
  rw [Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, by simpa only [mul_comm] using h.symm⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, by simpa only [mul_comm] using h.symm⟩

theorem two_x_even_constant : TwoXEvenConstant := by
  intro f hf
  obtain ⟨a, b, rfl⟩ := (two_x_representation f).mp hf
  exact ⟨a.coeff 0, by simp⟩

theorem strictness_witnesses : StrictnessWitnesses := by
  refine ⟨?_, Ideal.subset_span (by simp), ?_⟩
  · rw [Ideal.mem_span_singleton, ← evaluation_zero_iff_multiple]
    norm_num
  · intro h
    have heven := two_x_even_constant 1 h
    norm_num at heven

theorem strict_ideal_chain : StrictIdealChain := by
  have hle : (Ideal.span ({X} : Set (Polynomial ℤ)) : Ideal (Polynomial ℤ)) ≤
      Ideal.span ({C 2, X} : Set (Polynomial ℤ)) := by
    apply Ideal.span_le.mpr
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact Ideal.subset_span (by simp)
  refine ⟨lt_of_le_of_ne hle ?_, lt_top_iff_ne_top.mpr ?_⟩
  · intro h
    exact strictness_witnesses.1 (h ▸ strictness_witnesses.2.1)
  · intro h
    exact strictness_witnesses.2.2 (h ▸ (show (1 : Polynomial ℤ) ∈ (⊤ : Ideal _) from trivial))

end D07.Ch09.MaximalPrimeNonconverse
