import MathGenome.Internal.Specs.D07.Ch12.MinpolyDivisibility
import Mathlib.FieldTheory.Normal.Defs

/-!
Independent specification for K07.12.normal_definition
(paper.tex:3836–3848; chapters/M07.12.tex:295–307).

`Algebra K L` specifies the embedding of fields. We use the canonical
`Normal K L`, whose agreement with the source's irreducible-polynomial
definition is an obligation below. A root is evaluated using that same
embedding, and splitting means that the coefficient-mapped polynomial in
`L[X]` splits into linear factors. No finite-degree, separability, or
algebraically closed overfield hypothesis is imposed.

Algebraicity is part of normality. In the two criteria stated for algebraic
extensions it is an explicit hypothesis, so that the zero minimal polynomial
of a transcendental element cannot make the splitting criterion vacuous.
-/

universe u v

namespace Specs.D07.Ch12.NormalDefinition

/-- The source definition, including its algebraicity requirement. -/
def NormalExtensionCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Normal K L ↔
      Algebra.IsAlgebraic K L ∧
        ∀ f : Polynomial K, Irreducible f →
          (∃ a : L, Polynomial.aeval a f = 0) →
          (f.map (algebraMap K L)).Splits

/-- In an algebraic extension, normality is equivalent to splitting of every
element's minimal polynomial over the specified base. -/
def NormalIffMinimalPolynomialSplits : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Algebra.IsAlgebraic K L →
      (Normal K L ↔
        ∀ a : L, ((minpoly K a).map (algebraMap K L)).Splits)

/-- The irreducible-polynomial and minimal-polynomial criteria agree, under
exactly the algebraicity hypothesis of the source. -/
def IrreducibleCriterionIffMinimalPolynomialCriterion : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Algebra.IsAlgebraic K L →
      ((∀ f : Polynomial K, Irreducible f →
        (∃ a : L, Polynomial.aeval a f = 0) →
        (f.map (algebraMap K L)).Splits) ↔
      ∀ a : L, ((minpoly K a).map (algebraMap K L)).Splits)

end Specs.D07.Ch12.NormalDefinition
