import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Galois.Basic

namespace Specs.GaloisFormalization.IG.QuadraticPrimeFibres

open Polynomial

/-- A positive prime is nonsquare in the rational field. -/
def primeNonsquare : Prop :=
  ∀ {p : ℕ}, p.Prime → ¬ IsSquare (p : ℚ)

/-- The fibre at a positive prime has distinct roots over an algebraic closure. -/
def fibreSeparable : Prop :=
  ∀ {p : ℕ}, p.Prime → (X ^ 2 - C (p : ℚ)).Separable

/-- The group of a splitting field of the prime fibre is cyclic of order two. -/
def fibreGaloisGroup : Prop :=
  ∀ {p : ℕ}, p.Prime → ∀ (L : Type*) [Field L] [Algebra ℚ L]
    [IsSplittingField ℚ L (X ^ 2 - C (p : ℚ))],
    Nonempty ((L ≃ₐ[ℚ] L) ≃* Multiplicative (ZMod 2))

end Specs.GaloisFormalization.IG.QuadraticPrimeFibres
