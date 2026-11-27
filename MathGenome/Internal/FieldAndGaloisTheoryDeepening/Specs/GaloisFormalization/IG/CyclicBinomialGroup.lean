import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.GroupTheory.QuotientGroup.Defs

namespace GaloisFormalization.IG.CyclicBinomial

open Polynomial

variable (k : Type*) [Field k]

/-- `Xⁿ - t` with `t` the indeterminate of the coefficient field `k(t)`. -/
noncomputable def binomial (n : ℕ) : Polynomial (RatFunc k) :=
  X ^ n - C RatFunc.X

/-- Order at the prime `(t)`, with zeros counted positively and poles negatively. -/
noncomputable def orderAtT (u : (RatFunc k)ˣ) : ℤ :=
  -WithZero.log ((Polynomial.idealX k).valuation (RatFunc k) (u : RatFunc k))

/-- The indeterminate as a unit of `k(t)`. -/
noncomputable def tUnit : (RatFunc k)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero

/-- The class of `t` in `k(t)ˣ / (k(t)ˣ)ⁿ`. -/
noncomputable def tPowerClass (n : ℕ) : (RatFunc k)ˣ ⧸ (powMonoidHom n).range :=
  QuotientGroup.mk (tUnit k)

end GaloisFormalization.IG.CyclicBinomial

namespace Specs.GaloisFormalization.IG.CyclicBinomial

open _root_.GaloisFormalization.IG.CyclicBinomial

/-- The order at `(t)` is additive on products of nonzero rational functions. -/
def orderAtT_mul_type : Prop :=
  ∀ {k : Type*} [Field k] (u v : (RatFunc k)ˣ),
    orderAtT k (u * v) = orderAtT k u + orderAtT k v

/-- The order of the factor `t` itself is one. -/
def orderAtT_t_type : Prop :=
  ∀ {k : Type*} [Field k], orderAtT k (tUnit k) = 1

/-- If `tⁱ` is an `n`th power in `k(t)`, then `n` divides `i`. -/
def dvd_of_t_zpow_eq_pow_type : Prop :=
  ∀ {k : Type*} [Field k] (n : ℕ), 2 ≤ n → ∀ (i : ℤ) (x : RatFunc k),
    x ^ n = (RatFunc.X : RatFunc k) ^ i → (n : ℤ) ∣ i

/-- The class of `t` in the quotient by the `n`th powers has exact order `n`. -/
def orderOf_tPowerClass_type : Prop :=
  ∀ {k : Type*} [Field k] (n : ℕ), 2 ≤ n → orderOf (tPowerClass k n) = n

/-- The binomial is irreducible over `k(t)`. -/
def binomial_irreducible_type : Prop :=
  ∀ {k : Type*} [Field k] (n : ℕ), 2 ≤ n → Irreducible (binomial k n)

/-- The binomial is separable when `n` is invertible in `k`. -/
def binomial_separable_type : Prop :=
  ∀ {k : Type*} [Field k] (n : ℕ), 2 ≤ n → IsUnit (n : k) → (binomial k n).Separable

/-- Every splitting field of `Xⁿ - t` is finite Galois and has cyclic group of order `n`.
The constant field is arbitrary, so this includes algebraically closed constants. -/
def cyclic_splitting_field_type : Prop :=
  ∀ {k : Type*} [Field k] (n : ℕ), 2 ≤ n → IsUnit (n : k) → ∀ ζ : k, IsPrimitiveRoot ζ n →
    ∀ (L : Type*) [Field L] [Algebra (RatFunc k) L],
      Polynomial.IsSplittingField (RatFunc k) L (binomial k n) →
        FiniteDimensional (RatFunc k) L ∧ IsGalois (RatFunc k) L ∧
          Nonempty ((L ≃ₐ[RatFunc k] L) ≃* Multiplicative (ZMod n))

/-- The same group computation applies after extending the constant field, in particular
to the algebraic closure of the constants. The hypotheses on `n` and `ζ` are over `k`. -/
def cyclic_splitting_field_extend_constants_type : Prop :=
  ∀ {k : Type*} [Field k] (n : ℕ), 2 ≤ n → IsUnit (n : k) → ∀ ζ : k, IsPrimitiveRoot ζ n →
    ∀ (K : Type*) [Field K] [Algebra k K],
      ∀ (L : Type*) [Field L] [Algebra (RatFunc K) L],
        Polynomial.IsSplittingField (RatFunc K) L (binomial K n) →
          FiniteDimensional (RatFunc K) L ∧ IsGalois (RatFunc K) L ∧
            Nonempty ((L ≃ₐ[RatFunc K] L) ≃* Multiplicative (ZMod n))

end Specs.GaloisFormalization.IG.CyclicBinomial
