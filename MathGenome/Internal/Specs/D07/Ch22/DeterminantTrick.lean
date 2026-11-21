import MathGenome.Internal.Specs.D07.Ch22.DeterminantTrickStableFiniteSubmodule

/-!
Independent specification of K07.22.determinant_trick,
paper.tex:7185–7227 (chapters/M07.22.tex:489).

The rings are commutative and unital, and may be zero rings. The given
algebra map need not be injective. `C.toSubmodule.FG` means finite module
generation over R, rather than finite algebra generation or freeness.
The subalgebras contain the ambient identity, as required by the source.

`IntegralEquation` identifies the canonical predicate `IsIntegral` with
the source's equation having a positive displayed exponent. It does not
require positive formal polynomial degree in the zero coefficient ring.
The stable-submodule statement uses the shared upstream specification,
including its R[x]-faithfulness hypothesis and its common polynomial.
-/

universe u v

namespace Specs.D07.Ch22.DeterminantTrick

open Polynomial
open scoped BigOperators

/-- The explicit positive-exponent equation in the definition of integrality. -/
def IntegralEquation : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B] (x : B),
    IsIntegral R x ↔ ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → R,
      x ^ n + ∑ i ∈ Finset.range n, algebraMap R B (a i) * x ^ i = 0

/-- All three conditions in the integral-finite theorem are equivalent. -/
def IntegralFiniteEquivalences : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B] (x : B),
    (IsIntegral R x ↔ (Algebra.adjoin R ({x} : Set B)).toSubmodule.FG) ∧
    (IsIntegral R x ↔
      ∃ C : Subalgebra R B, x ∈ C ∧ C.toSubmodule.FG)

/-- The determinant trick, with its two sufficient conditions for an
equation for x, as specified by the shared stable-submodule interface. -/
def StableFiniteSubmodule : Prop :=
  Specs.D07.Ch22.DeterminantTrickStableFiniteSubmodule.StableFiniteSubmodule.{u, v}

end Specs.D07.Ch22.DeterminantTrick
