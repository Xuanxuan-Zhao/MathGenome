import MathGenome.Internal.Specs.D07.Ch12.AlgebraicDefinition
import Mathlib.FieldTheory.Minpoly.Basic

/-!
Independent specification for K07.12.minpoly_existence
(paper.tex:3583–3592; chapters/M07.12.tex:42–51).

`Algebra K L` records the specified field embedding; `Polynomial.aeval α`
uses that embedding. Algebraicity is the upstream nonzero-annihilator
predicate, not an assumed monic or irreducible annihilator. The fields and
the algebraic element are arbitrary: the whole extension need not be
algebraic or finite, and no algebraically closed overfield is chosen.

The canonical `minpoly K α` represents the polynomial named in the source.
Degree is the bottom-valued polynomial degree used by the upstream Specs.
Existential uniqueness below ranges over all monic irreducible annihilators,
without placing positive degree among the conditions restricting uniqueness.
-/

universe u v

namespace Specs.D07.Ch12.MinpolyExistence

/-- The named minimal polynomial has every property asserted in the source. -/
def MinimalPolynomialProperties : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    IsAlgebraic K α →
      (minpoly K α).Monic ∧ Irreducible (minpoly K α) ∧
      Polynomial.aeval α (minpoly K α) = 0 ∧ 0 < (minpoly K α).degree

/-- Every monic irreducible annihilator is the named minimal polynomial. -/
def MinimalPolynomialUniqueness : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    IsAlgebraic K α →
      ∀ p : Polynomial K, p.Monic → Irreducible p →
        Polynomial.aeval α p = 0 → p = minpoly K α

/-- Existence and uniqueness with no choice of a preferred overfield. -/
def UniqueMonicIrreducibleAnnihilator : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    IsAlgebraic K α →
      ∃! p : Polynomial K,
        p.Monic ∧ Irreducible p ∧ Polynomial.aeval α p = 0

end Specs.D07.Ch12.MinpolyExistence
