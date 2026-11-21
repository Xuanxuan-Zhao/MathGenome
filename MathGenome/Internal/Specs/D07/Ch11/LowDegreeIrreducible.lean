import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.Field.Rat

/-!
Independent specification of K07.11.low_degree_irreducible
(paper.tex:2466–2478; chapters/M07.11.tex:321–333).

All polynomials are formal polynomials with their canonical operations.
The field is arbitrary, without restrictions on characteristic or cardinality.
The degree hypotheses use bottom-valued degree and thus exclude zero.
The final statement records the specific rational counterexample from the source.
-/

universe u

namespace Specs.D07.Ch11.LowDegreeIrreducible

open Polynomial

def DegreeOneIrreducible : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F),
    f.degree = (1 : WithBot ℕ) → Irreducible f

def DegreeTwoOrThreeIffNoRoot : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F),
    (f.degree = (2 : WithBot ℕ) ∨ f.degree = (3 : WithBot ℕ)) →
      (Irreducible f ↔ ∀ a : F, f.eval a ≠ 0)

/-- A rootless reducible polynomial of degree four, over the stated field ℚ. -/
def RationalQuarticCounterexample : Prop :=
  let f : Polynomial ℚ := (X ^ 2 + 1) ^ 2
  f.degree = (4 : WithBot ℕ) ∧
    (∀ a : ℚ, f.eval a ≠ 0) ∧ ¬ Irreducible f

end Specs.D07.Ch11.LowDegreeIrreducible
