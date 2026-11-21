import MathGenome.Internal.Specs.D07.Ch08.IdealProduct
import MathGenome.Internal.Specs.D07.Ch11.PolynomialArithmetic
import Mathlib.RingTheory.Nilpotent.Defs

/-!
Independent specification of the sufficiency argument in
K07.11.polynomial_units, paper.tex:2299–2310.
The ideal power is the canonical product power, and the polynomial is the
formal polynomial of the upstream specifications. All statements allow the
zero ring. In particular, the finite family may be empty and the polynomial
may be constant (or zero in the zero ring).
-/

universe u v

namespace Specs.D07.Ch11.PolynomialUnitsNilpotentCoefficientIdeal

/-- The stated sharp uniform bound for a finite family of nilpotent
coefficients. Only the exponents of members of `s` are constrained.
The ideal is generated in the entire ambient commutative ring. -/
def FiniteFamilyIdealNilpotence : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) (s : Finset ι)
    (a : ι → R) (e : ι → ℕ),
    (∀ i ∈ s, 1 ≤ e i) → (∀ i ∈ s, a i ^ e i = 0) →
    (Ideal.span (a '' (↑s : Set ι))) ^ (1 + ∑ i ∈ s, (e i - 1)) = ⊥

/-- Convolution puts every coefficient of the nth polynomial power in
`J^n` when the original coefficients lie in `J`, including `n = 0`. -/
def CoefficientsOfPowers : Prop :=
  ∀ (R : Type u) [CommRing R] (J : Ideal R) (f : Polynomial R),
    (∀ k, f.coeff k ∈ J) →
    ∀ n k, (f ^ n).coeff k ∈ J ^ n

/-- The bridge used in the paper: a nilpotent coefficient ideal kills
the corresponding power of the polynomial. -/
def PolynomialPowerVanishes : Prop :=
  ∀ (R : Type u) [CommRing R] (J : Ideal R) (f : Polynomial R) (N : ℕ),
    (∀ k, f.coeff k ∈ J) → J ^ N = ⊥ → f ^ N = 0

/-- Unit constant coefficient and nilpotent positive-degree coefficients
suffice for a two-sided inverse in the formal polynomial ring. -/
def PolynomialInverse : Prop :=
  ∀ (R : Type u) [CommRing R] (f : Polynomial R),
    IsUnit (f.coeff 0) →
    (∀ i : ℕ, 0 < i → IsNilpotent (f.coeff i)) →
    ∃ g : Polynomial R, f * g = 1 ∧ g * f = 1

end Specs.D07.Ch11.PolynomialUnitsNilpotentCoefficientIdeal
