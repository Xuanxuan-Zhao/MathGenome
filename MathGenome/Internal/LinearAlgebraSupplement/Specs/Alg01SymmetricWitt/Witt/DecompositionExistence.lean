import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Coordinates

namespace Specs.Alg01SymmetricWitt.Witt.DecompositionExistence

open Coordinates (hyperbolicSum)

universe u v

/-- A finite-dimensional nondegenerate space decomposes into hyperbolic planes and
an anisotropic subspace with its restricted form. An anisotropic space needs zero planes. -/
def wittDecompositionExists : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (q : QuadraticForm k V), q.Nondegenerate →
    ∃ (r : ℕ) (A : Submodule k V),
      (q.comp A.subtype).Anisotropic ∧ (q.comp A.subtype).Nondegenerate ∧
      Nonempty (q.IsometryEquiv ((hyperbolicSum k r).prod (q.comp A.subtype))) ∧
      (q.Anisotropic → r = 0)

end Specs.Alg01SymmetricWitt.Witt.DecompositionExistence
