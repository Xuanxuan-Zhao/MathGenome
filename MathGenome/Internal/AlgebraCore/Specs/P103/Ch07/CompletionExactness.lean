import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletionInterface
import Mathlib.Algebra.Exact.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! The exactness assertion of Theorem 7.4, paper.tex:1209–1224.
The tensor comparison is allocated separately. Finiteness means finite
generation, and no localness, separatedness, or Jacobson condition is imposed.
-/

universe u v w z

namespace P103.Specs.Ch07.CompletionExactness

/-- The canonical completion maps preserve all three parts of short exactness.
`AdicCompletion.map` is exactly the completed map of the shared completion
interface; in particular these maps are linear over the completed ring.
The three modules may inhabit independent universes. Zero rings, zero modules,
and the zero and unit ideals are included. -/
def short_exactType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (A : Type v) [AddCommGroup A] [Module R A] [Module.Finite R A]
    (B : Type w) [AddCommGroup B] [Module R B] [Module.Finite R B]
    (C : Type z) [AddCommGroup C] [Module R C] [Module.Finite R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
      Function.Injective (AdicCompletion.map I f) ∧
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
      Function.Surjective (AdicCompletion.map I g)

end P103.Specs.Ch07.CompletionExactness
