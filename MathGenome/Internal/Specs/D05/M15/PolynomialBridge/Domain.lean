import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import MathGenome.Internal.Specs.D05.M15.SymmetricBasis
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statements for paper.tex:3038 (K05.15.polynomial_bridge).
These concern formal coefficient polynomials and the existing symmetric algebra,
over any field. In particular there is no infinitude or characteristic hypothesis.
All natural numbers of variables are allowed, including zero.
-/

namespace Specs.D05.M15.PolynomialBridge.Domain

open D05.Foundations
open Specs.D05.M15.Symmetric

universe u v

/-- The formal polynomial ring, including its nontriviality, is a domain. -/
def formal_polynomial_domain : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ), IsDomain (FormalPolynomial K n)

/-- Nonzero finite formal polynomials have nonzero product. -/
def formal_polynomial_mul_ne_zero : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (p q : FormalPolynomial K n),
    p ≠ 0 → q ≠ 0 → p * q ≠ 0

/-- In the upstream finite coefficient-array model, the convolution has a
nonzero coefficient whenever both arrays are nonzero. -/
def coefficient_convolution_nonzero : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (a b : PolynomialCoefficients K n),
    a ≠ 0 → b ≠ 0 → ∃ γ : Exponent n,
      (∑ ab ∈ exponentSplittings γ, a.coeff ab.1 * b.coeff ab.2) ≠ 0

/-- The monomial-coordinate algebra equivalence transfers the domain property
for any supplied finite basis, including the empty basis. -/
def symmetric_domain_of_basis : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (_b : Module.Basis (Fin n) K V), IsDomain (symmetricAlgebra K V)

/-- Basis-free formulation of the conclusion for every finite-dimensional V. -/
def symmetric_domain : Prop :=
  ∀ (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], IsDomain (symmetricAlgebra K V)

end Specs.D05.M15.PolynomialBridge.Domain
