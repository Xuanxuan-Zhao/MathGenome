import MathGenome.Internal.Specs.D07.Ch22.DeterminantTrick
import Mathlib.RingTheory.Finiteness.Basic

/-!
K07.22.integral_closure_transitivity, paper.tex:7230–7254, first paragraph
of the proof. All algebras here are commutative and unital, with no
nontriviality or injectivity assumption. The bounds n i are the positive
*displayed exponents* in the equations, not formal polynomial degrees.
The empty tuple is allowed; its sole monomial is the empty product 1.
-/

universe u v
namespace Specs.D07.Ch22.IntegralClosureTransitivityFiniteIntegralGeneration
open scoped BigOperators

/-- The exact finite list of bounded monomials spans the generated algebra. -/
def BoundedMonomialSpan : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (t : ℕ) (x : Fin t → B) (n : Fin t → ℕ) (a : Fin t → ℕ → R),
    (∀ i, 0 < n i) →
    (∀ i, x i ^ n i + ∑ k ∈ Finset.range (n i),
      algebraMap R B (a i k) * x i ^ k = 0) →
    (Algebra.adjoin R (Set.range x)).toSubmodule =
      Submodule.span R (Set.range fun e : (i : Fin t) → Fin (n i) =>
        ∏ i, x i ^ (e i : ℕ))

/-- A finite tuple of integral generators gives a finite module. -/
def FiniteIntegralGeneration : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (t : ℕ) (x : Fin t → B),
    (∀ i, IsIntegral R (x i)) → (Algebra.adjoin R (Set.range x)).toSubmodule.FG

/-- Every element of a module-finite algebra is integral. -/
def FiniteAlgebraIntegral : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (x : B), IsIntegral R x

/-- Explicit closure under the base scalars and the stated ring operations. -/
def IntegralOperations : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B],
    (∀ r : R, IsIntegral R (algebraMap R B r)) ∧
    (∀ x y : B, IsIntegral R x → IsIntegral R y →
      IsIntegral R (x + y) ∧ IsIntegral R (x * y) ∧ IsIntegral R (x - y)) ∧
    (∀ x : B, IsIntegral R x → IsIntegral R (-x))

/-- The integral elements, with exactly that carrier, form a subalgebra. -/
def IntegralElementsSubalgebra : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B],
    ∃ S : Subalgebra R B, ∀ x : B, x ∈ S ↔ IsIntegral R x

end Specs.D07.Ch22.IntegralClosureTransitivityFiniteIntegralGeneration
