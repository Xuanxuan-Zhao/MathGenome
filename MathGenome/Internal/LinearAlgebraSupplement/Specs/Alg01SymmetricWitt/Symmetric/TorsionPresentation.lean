import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Algebra
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation

noncomputable section

open Polynomial
open scoped Polynomial DirectSum
open Specs.Alg01SymmetricWitt.Symmetric.Algebra (degree)

/-- The relation imposed by twice the cyclic generator. -/
def relationIdeal : Ideal ℤ[X] := Ideal.span {C 2 * X}

/-- The polynomial quotient in the torsion example. -/
abbrev PolynomialQuotient := ℤ[X] ⧸ relationIdeal

def quotientMap : ℤ[X] →ₐ[ℤ] PolynomialQuotient :=
  Ideal.Quotient.mkₐ ℤ relationIdeal

/-- The usual homogeneous polynomials of degree `n` in one variable. -/
def polynomialDegree (n : ℕ) : Submodule ℤ ℤ[X] :=
  LinearMap.range (monomial n : ℤ →ₗ[ℤ] ℤ[X])

/-- The images of the usual polynomial degrees under the quotient map. -/
def quotientDegree (n : ℕ) : Submodule ℤ PolynomialQuotient :=
  (polynomialDegree n).map quotientMap.toLinearMap

def presentation : Prop :=
  ∃ e : SymmetricAlgebra ℤ (ZMod 2) ≃ₐ[ℤ] PolynomialQuotient,
    e (SymmetricAlgebra.ι ℤ (ZMod 2) 1) = quotientMap X ∧
    ∀ n : ℕ, (degree ℤ (ZMod 2) n).map e.toLinearMap = quotientDegree n

/-- The quotient decomposition takes each polynomial to the classes of its homogeneous terms. -/
def quotientGrading : Prop :=
  ∃ g : GradedAlgebra quotientDegree,
    letI := g
    ∀ (p : ℤ[X]) (n : ℕ),
      (DirectSum.decompose quotientDegree (quotientMap p) n : PolynomialQuotient) =
        quotientMap (monomial n (p.coeff n))

def degreeZero : Prop :=
  ∃ g : GradedAlgebra quotientDegree,
    letI := g
    ∃ e : ℤ ≃ₐ[ℤ] quotientDegree 0,
      ∀ a : ℤ, (e a : PolynomialQuotient) = quotientMap (C a)

def degreePositive : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ e : ZMod 2 ≃ₗ[ℤ] quotientDegree n,
      ∀ a : ℤ, (e (a : ZMod 2) : PolynomialQuotient) = quotientMap (monomial n a)

end

end Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation
