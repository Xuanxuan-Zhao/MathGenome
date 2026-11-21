import MathGenome.Internal.Specs.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.Specs.D07.Ch16.MapsSubmodules
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
Independent specification of the stable finite submodule determinant trick,
K07.22.determinant_trick, paper.tex:7185–7227.

`M.FG` means finitely generated as an R-module, not free. Stability is
multiplication by the specified ambient element x. The coefficients below
are in R and evaluation uses the given algebra map R → B. The displayed
exponent n is positive even for the zero module and zero coefficient ring;
no positive formal degree of the zero polynomial is required.

Faithfulness is written as injectivity of the multiplication action of
`Algebra.adjoin R {x}` on M: two elements with identical multiplication
on every member of M are equal. Stability under x implies stability under
this whole subalgebra. This formulation avoids choosing another module
structure on M, and does not replace R[x]-faithfulness by R-faithfulness.
All conclusions concern the same explicitly displayed polynomial p.
-/

universe u v

namespace Specs.D07.Ch22.DeterminantTrickStableFiniteSubmodule

open Polynomial
open scoped BigOperators

/-- A positive-exponent monic annihilator, with the two stated sufficient
conditions for it to be an equation for x itself. -/
def StableFiniteSubmodule : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (x : B) (M : Submodule R B),
    M.FG → (∀ m ∈ M, x * m ∈ M) →
    ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → R,
      let p : R[X] := X ^ n + ∑ i ∈ Finset.range n, C (a i) * X ^ i
      p.Monic ∧
      (∀ m ∈ M, aeval x p * m = 0) ∧
      (1 ∈ M → aeval x p = 0 ∧ IsIntegral R x) ∧
      ((∀ y z : Algebra.adjoin R ({x} : Set B),
          (∀ m ∈ M, (y : B) * m = (z : B) * m) → y = z) →
        aeval x p = 0 ∧ IsIntegral R x)

end Specs.D07.Ch22.DeterminantTrickStableFiniteSubmodule
