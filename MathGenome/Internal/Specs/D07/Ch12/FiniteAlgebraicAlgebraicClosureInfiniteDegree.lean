import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
Independent statements for the counterexample in K07.12.finite_algebraic
(paper.tex:3575–3582) and the assigned failure of an unrestricted algebraic
primitive-element assertion. The extension always uses its specified algebra
map. Infinite degree is expressed using cardinal dimension, never the default
value of `finrank` on an infinite-dimensional vector space.

An algebraic closure here means an algebraic extension that is algebraically
closed, exactly as in the upstream algebraic-closure specification. The root
statements also apply to arbitrary algebraically closed overfields of ℚ.
-/

universe u

namespace Specs.D07.Ch12.FiniteAlgebraicAlgebraicClosureInfiniteDegree

/-- Every root of X^m - 2 has that polynomial as its minimal polynomial and
generates a degree-m extension. In particular, no choice of root matters. -/
def RootDegree : Prop :=
  ∀ (L : Type u) [Field L] [Algebra ℚ L] (m : ℕ), 1 ≤ m →
    ∀ α : L, α ^ m = (2 : L) →
      minpoly ℚ α = Polynomial.X ^ m - Polynomial.C (2 : ℚ) ∧
      Module.rank ℚ (IntermediateField.adjoin ℚ {α}) = (m : Cardinal.{u})

/-- Each positive degree is realized by a root of X^m - 2 inside the given
closed field, with its minimal polynomial and cardinal simple degree specified. -/
def RootsOfEveryDegree : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω]
    (m : ℕ), 1 ≤ m →
      ∃ α : Ω, α ^ m = (2 : Ω) ∧
        minpoly ℚ α = Polynomial.X ^ m - Polynomial.C (2 : ℚ) ∧
        Module.rank ℚ (IntermediateField.adjoin ℚ {α}) = (m : Cardinal.{u})

/-- Every algebraic closure of ℚ is algebraic of infinite cardinal degree and
has no generator as an extension of ℚ. Both standard meanings of infinite
degree (no natural cardinal degree, and degree at least aleph₀) are recorded. -/
def ClosureInfiniteAndNotSimple : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [IsAlgClosed Ω],
      Algebra.IsAlgebraic ℚ Ω ∧
      (¬ ∃ n : ℕ, Module.rank ℚ Ω = (n : Cardinal.{u})) ∧
      Cardinal.aleph0 ≤ Module.rank ℚ Ω ∧
      ∀ α : Ω, IntermediateField.adjoin ℚ {α} ≠ ⊤

/-- An actual extension witnesses failure of both proposed implications:
algebraic ⇒ finite, and algebraic ⇒ simple. No closedness assumption on ℂ
or other analytic fact enters this existential assertion. -/
def CounterexampleExists : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L),
    IsAlgClosed L ∧ Algebra.IsAlgebraic ℚ L ∧
      (¬ ∃ n : ℕ, Module.rank ℚ L = (n : Cardinal)) ∧
      ∀ α : L, IntermediateField.adjoin ℚ {α} ≠ ⊤

end Specs.D07.Ch12.FiniteAlgebraicAlgebraicClosureInfiniteDegree
