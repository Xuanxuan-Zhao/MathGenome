import Mathlib.Data.Int.Basic
import Mathlib.Basic.ExistsUnique

/-!
# Division with remainder: independent specification

Source: `paper.tex`, Lemma 1.1 (`nt:division`), with the integer and
positive-modulus conventions preceding it. Integer operations are the standard
ones; in particular the dividend is allowed to be negative.
-/

namespace P203Specs.Ch01

/-- Every integer has a unique quotient and nonnegative remainder for a
positive integer modulus. Uniqueness is joint uniqueness of the pair `(q, r)`. -/
def DivisionWithRemainder : Prop :=
  ∀ (a m : ℤ), 0 < m →
    ∃! qr : ℤ × ℤ, a = qr.1 * m + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < m

end P203Specs.Ch01
