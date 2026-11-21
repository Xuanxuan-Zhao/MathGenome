import MathGenome.Internal.Specs.D07.Ch11.PolynomialDefinition
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Complex.Module

/-!
Independent specifications for K07.11.irreducible_quotient,
paper.tex:2744–2780. All quotients carry their canonical ring operations;
`IsField` includes nontriviality. Positive natural degree expresses
nonconstancy without treating the zero polynomial as degree zero.
The example uses an ℝ-algebra equivalence and specifies its coordinate
formula. General normal-form and dimension statements belong to the next entry.
-/

universe u

namespace Specs.D07.Ch11.IrreducibleQuotient

open Polynomial

/-- The field criterion for an arbitrary, possibly nonmonic, nonconstant polynomial. -/
def QuotientFieldIffIrreducible : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), 0 < f.natDegree →
    (IsField (Polynomial F ⧸ Ideal.span {f}) ↔ Irreducible f)

/-- The class of X is a root with coefficients mapped to constant classes.
This identity also holds for zero and constant polynomials. -/
def QuotientRootEquation : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F),
    f.eval₂ ((Ideal.Quotient.mk (Ideal.span {f})).comp C)
      (Ideal.Quotient.mk (Ideal.span {f}) X) = 0

/-- A reducible positive-degree polynomial gives actual nonzero zero divisors,
represented by proper positive-degree factors. -/
def ReducibleQuotientZeroDivisors : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), 0 < f.natDegree →
    ¬ Irreducible f → ∃ g h : Polynomial F,
      f = g * h ∧ 0 < g.natDegree ∧ 0 < h.natDegree ∧
      g.natDegree < f.natDegree ∧ h.natDegree < f.natDegree ∧
      Ideal.Quotient.mk (Ideal.span {f}) g ≠ 0 ∧
      Ideal.Quotient.mk (Ideal.span {f}) h ≠ 0 ∧
      Ideal.Quotient.mk (Ideal.span {f}) g *
        Ideal.Quotient.mk (Ideal.span {f}) h = 0

/-- Quotienting by zero recovers the polynomial domain; X remains a nonunit. -/
def ZeroPolynomialQuotient : Prop :=
  ∀ (F : Type u) [Field F],
    (∃ e : (Polynomial F ⧸ Ideal.span {(0 : Polynomial F)}) ≃+* Polynomial F,
      ∀ p, e (Ideal.Quotient.mk (Ideal.span {(0 : Polynomial F)}) p) = p) ∧
    IsDomain (Polynomial F ⧸ Ideal.span {(0 : Polynomial F)}) ∧
    ¬ IsField (Polynomial F ⧸ Ideal.span {(0 : Polynomial F)}) ∧
    ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {(0 : Polynomial F)}) X)

/-- A nonzero constant is a unit; its quotient is the zero ring and is not a field. -/
def NonzeroConstantQuotient : Prop :=
  ∀ (F : Type u) [Field F] (a : F), a ≠ 0 →
    IsUnit (C a) ∧
    Subsingleton (Polynomial F ⧸ Ideal.span {C a}) ∧
    ¬ IsField (Polynomial F ⧸ Ideal.span {C a})

/-- The example includes α²=-1, a genuine algebra isomorphism with ℂ,
the displayed a+bα ↦ a+bi formula, and unique such coordinates. -/
def RealQuadraticExample : Prop :=
  let f : Polynomial ℝ := X ^ 2 + 1
  let Q := Polynomial ℝ ⧸ Ideal.span {f}
  let α : Q := Ideal.Quotient.mk (Ideal.span {f}) X
  IsField Q ∧ α ^ 2 = -1 ∧
    ∃ e : Q ≃ₐ[ℝ] ℂ,
      e α = Complex.I ∧
      (∀ a b : ℝ, e (algebraMap ℝ Q a + algebraMap ℝ Q b * α) =
        (a : ℂ) + (b : ℂ) * Complex.I) ∧
      ∀ x : Q, ∃! ab : ℝ × ℝ,
        x = algebraMap ℝ Q ab.1 + algebraMap ℝ Q ab.2 * α

end Specs.D07.Ch11.IrreducibleQuotient
