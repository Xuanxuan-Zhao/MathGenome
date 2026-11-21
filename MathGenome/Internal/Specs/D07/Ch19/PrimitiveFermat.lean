import Mathlib.Algebra.Polynomial.FieldDivision

/-!
Independent statement of K07.19.primitive_fermat,
paper.tex:5772–5785 (chapters/M07.19.tex:540).

All three polynomials are nonzero and pairwise coprime over the original
characteristic-zero field. Constancy is expressed by equality to actual
constant polynomials, without passing to a quotient or removing a factor.
The common-factor classification and the complex counterexample are stated
separately in `Specs.D07.Ch19.PrimitiveFermatCommonFactorClassification`.
-/

universe u

namespace Specs.D07.Ch19.PrimitiveFermat

open Polynomial

/-- A nonzero primitive polynomial Fermat solution of exponent at least three
consists of three constant polynomials over the same coefficient field. -/
def PrimitiveFermat : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (n : ℕ), 3 ≤ n →
    ∀ f g h : Polynomial F, f ≠ 0 → g ≠ 0 → h ≠ 0 →
      IsCoprime f g → IsCoprime f h → IsCoprime g h →
      f ^ n + g ^ n = h ^ n →
      ∃ a b c : F, f = C a ∧ g = C b ∧ h = C c

end Specs.D07.Ch19.PrimitiveFermat
