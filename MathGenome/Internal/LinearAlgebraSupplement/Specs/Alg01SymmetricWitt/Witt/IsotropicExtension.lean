import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Coordinates

namespace Specs.Alg01SymmetricWitt.Witt.IsotropicExtension

open Coordinates (hyperbolicSum firstCoordinates totallyIsotropic)

universe u v

/-- A totally isotropic subspace is the sum of the first coordinate lines of an
orthogonal sum of hyperbolic planes, with a nondegenerate orthogonal complement. -/
def isotropicExtension : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (q : QuadraticForm k V), q.Nondegenerate →
    ∀ T : Submodule k V, totallyIsotropic q T →
    let m := Module.finrank k T
    ∃ (C : Submodule k V)
      (i : ((hyperbolicSum k m).prod (q.comp C.subtype)).IsometryEquiv q),
      (q.comp C.subtype).Nondegenerate ∧
      (∀ c : C, i (0, c) = (c : V)) ∧
      ∀ (x : Fin m → k × k) (c : C),
        i (x, c) ∈ T ↔ x ∈ firstCoordinates k m ∧ c = 0

end Specs.Alg01SymmetricWitt.Witt.IsotropicExtension
