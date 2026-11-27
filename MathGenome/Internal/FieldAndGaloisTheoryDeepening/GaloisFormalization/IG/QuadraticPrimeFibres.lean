import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.KummerPolynomial

namespace GaloisFormalization.IG

open Polynomial

/-- A positive prime is nonsquare in the rational field. -/
theorem prime_not_isSquare_rat {p : ℕ} (hp : p.Prime) : ¬ IsSquare (p : ℚ) :=
  fun h ↦ hp.prime.not_isSquare (Rat.isSquare_natCast_iff.mp h)

/-- The fibre of `X² - t` at a positive prime is separable over ℚ. -/
theorem quadratic_prime_fibre_separable {p : ℕ} (hp : p.Prime) :
    (X ^ 2 - C (p : ℚ)).Separable :=
  separable_X_pow_sub_C (p : ℚ) (by decide) (Nat.cast_ne_zero.mpr hp.ne_zero)

/-- Every splitting field of the prime fibre has Galois group cyclic of order two. -/
theorem quadratic_prime_fibre_galoisGroup {p : ℕ} (hp : p.Prime)
    (L : Type*) [Field L] [Algebra ℚ L] [IsSplittingField ℚ L (X ^ 2 - C (p : ℚ))] :
    Nonempty ((L ≃ₐ[ℚ] L) ≃* Multiplicative (ZMod 2)) := by
  have hirr : Irreducible (X ^ 2 - C (p : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two
      (fun b hb ↦ prime_not_isSquare_rat hp ⟨b, by simpa only [pow_two] using hb.symm⟩)
  have hζ : IsPrimitiveRoot (-1 : ℚ) 2 := IsPrimitiveRoot.neg_one 0 (by decide)
  exact ⟨autEquivZmod hirr L hζ⟩

end GaloisFormalization.IG
