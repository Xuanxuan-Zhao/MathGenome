import MathGenome.Internal.Specs.D07.Ch11.PolynomialDefinition

/-!
Formal polynomials over an arbitrary unital ring, K07.11.polynomial_definition.
Mathlib's polynomial is a wrapper around `AddMonoidAlgebra R ℕ`, whose
coefficients form a `Finsupp`. The sequence characterization below checks both
directions of this representation explicitly. No commutativity or
nontriviality instance is used, and no evaluation function is involved.
-/

universe u

namespace D07.Ch11.PolynomialDefinition

open Polynomial
open Specs.D07.Ch11.PolynomialDefinition

theorem finiteCoefficientSupport : FiniteCoefficientSupport.{u} := by
  intro R _ f
  exact f.coeff.hasFiniteSupport

theorem coefficientSequenceCharacterization : CoefficientSequenceCharacterization.{u} := by
  intro R _ a
  constructor
  · rintro ⟨f, hf, _⟩
    have heq : (fun i => f.coeff i) = a := funext hf
    rw [← heq]
    exact finiteCoefficientSupport R f
  · intro ha
    refine ⟨Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
      (Finsupp.ofSupportFinite a ha)), ?_, ?_⟩
    · intro i
      rfl
    · intro g hg
      apply Polynomial.ext
      intro i
      exact hg i

theorem coefficientExtensionality : CoefficientExtensionality.{u} := by
  intro R _ f g
  exact Polynomial.ext_iff

theorem constantCoefficients : ConstantCoefficients.{u} := by
  intro R _ a i
  exact Polynomial.coeff_C

theorem indeterminateCoefficients : IndeterminateCoefficients.{u} := by
  intro R _ i
  simpa only [eq_comm] using (Polynomial.coeff_X (R := R) (n := i))

theorem constantInjectivity : ConstantInjectivity.{u} := by
  intro R _
  exact Polynomial.C_injective

theorem boundedExpansion : BoundedExpansion.{u} := by
  intro R _ f n hz
  calc
    f = f.sum (fun i a => C a * X ^ i) := (Polynomial.sum_C_mul_X_pow_eq f).symm
    _ = ∑ i ∈ Finset.range (n + 1), C (f.coeff i) * X ^ i := by
      apply Polynomial.sum_eq_of_subset (fun i a => C a * X ^ i)
        (by intro i; simp)
      intro i hi
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply Nat.le_of_not_gt
      intro hni
      exact (Polynomial.mem_support_iff.mp hi) (hz i hni)

theorem finiteExpansion : FiniteExpansion.{u} := by
  intro R _ f
  refine ⟨f.support.sup id, boundedExpansion R f _ ?_⟩
  intro i hi
  by_contra hne
  have hle : i ≤ f.support.sup id :=
    Finset.le_sup (f := id) (Polynomial.mem_support_iff.mpr hne)
  exact (Nat.not_le_of_gt hi) hle

theorem trailingZeroIndependence : TrailingZeroIndependence.{u} := by
  intro R _ a n m hnm hz
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hnm))
  intro i him hin
  have hni : n < i := Nat.lt_of_not_ge (fun hi =>
    hin (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  have him' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp him)
  simp only [hz i hni him', map_zero, zero_mul]

end D07.Ch11.PolynomialDefinition
