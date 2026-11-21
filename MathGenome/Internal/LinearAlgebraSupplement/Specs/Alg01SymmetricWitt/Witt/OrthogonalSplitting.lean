import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Coordinates
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace Specs.Alg01SymmetricWitt.Witt.OrthogonalSplitting

universe u v

set_option linter.checkUnivs false in
def orthogonalComplementType :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V], QuadraticForm k V → Submodule k V → Submodule k V

/-- The orthogonal complement for the normalized associated bilinear form. -/
def orthogonalComplement : orthogonalComplementType.{u, v} :=
  fun q U => LinearMap.BilinForm.orthogonal q.associated U

/-- Membership in the complement, with the vector in the first slot of the pairing. -/
def mem_orthogonalComplement : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] (q : QuadraticForm k V) (U : Submodule k V) (x : V),
    x ∈ orthogonalComplement q U ↔ ∀ u ∈ U, q.associated x u = 0

/-- A nondegenerate subspace splits via addition and has nondegenerate orthogonal complement. -/
def orthogonalSplitting : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (q : QuadraticForm k V) (U : Submodule k V),
    q.Nondegenerate → (q.comp U.subtype).Nondegenerate →
    let W := orthogonalComplement q U
    IsCompl U W ∧
      (∃ e : ((q.comp U.subtype).prod (q.comp W.subtype)).IsometryEquiv q,
        ∀ z : U × W, e z = (z.1 : V) + (z.2 : V)) ∧
      (q.comp W.subtype).Nondegenerate

end Specs.Alg01SymmetricWitt.Witt.OrthogonalSplitting
