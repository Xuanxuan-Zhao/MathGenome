import MathGenome.Internal.Specs.D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
The generic polynomial in paper.tex:6136–6152, over every field.
`tuplePolynomial` is the alternating monic expression with the prescribed
independent coefficients, over their generated intermediate field. All scalar
maps are the given ones. No characteristic restriction is imposed.
-/

universe u v w

namespace Specs.D07.Ch20.GenericGroupAnyCharacteristic

open Specs.D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField

/-- The displayed polynomial has degree n and no repeated roots. -/
def GenericPolynomialProperties : Prop :=
  ∀ (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M]
    (n : ℕ), 1 ≤ n → ∀ (s : Fin n → M), AlgebraicIndependent K s →
    (tuplePolynomial K n M s).Monic ∧
    (tuplePolynomial K n M s).natDegree = n ∧
    (tuplePolynomial K n M s).Separable

/-- The polynomial Galois group is S_n, including characteristics dividing n!. -/
def GenericGaloisGroup : Prop :=
  ∀ (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M]
    (n : ℕ), 1 ≤ n → ∀ (s : Fin n → M), AlgebraicIndependent K s →
    Nonempty ((tuplePolynomial K n M s).Gal ≃* Equiv.Perm (Fin n))

/-- Every splitting field with its specified coefficient embedding has degree n!. -/
def GenericSplittingFieldDegree : Prop :=
  ∀ (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M]
    (n : ℕ), 1 ≤ n → ∀ (s : Fin n → M), AlgebraicIndependent K s →
    ∀ (L : Type w) [Field L]
      [Algebra (IntermediateField.adjoin K (Set.range s)) L]
      [Polynomial.IsSplittingField (IntermediateField.adjoin K (Set.range s)) L
        (tuplePolynomial K n M s)],
    FiniteDimensional (IntermediateField.adjoin K (Set.range s)) L ∧
    IsGalois (IntermediateField.adjoin K (Set.range s)) L ∧
    Module.finrank (IntermediateField.adjoin K (Set.range s)) L = n.factorial

end Specs.D07.Ch20.GenericGroupAnyCharacteristic
