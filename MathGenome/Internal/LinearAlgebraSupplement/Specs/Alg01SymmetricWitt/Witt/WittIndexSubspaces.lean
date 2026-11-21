import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Decomposition

namespace Specs.Alg01SymmetricWitt.Witt.WittIndexSubspaces

open Coordinates (hyperbolicSum firstCoordinates totallyIsotropic)
open Decomposition (IsWittIndex)

universe u v

/-- The Witt index bounds and attains the dimensions of totally isotropic subspaces.
Every such subspace admits an adapted splitting, and maximal ones attain the bound. -/
def wittIndexSubspaces : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (q : QuadraticForm k V), q.Nondegenerate → ∀ r : ℕ, IsWittIndex q r →
    (∀ T : Submodule k V, totallyIsotropic q T →
      let m := Module.finrank k T
      (∃ (C : Submodule k V)
        (i : ((hyperbolicSum k m).prod (q.comp C.subtype)).IsometryEquiv q),
        (q.comp C.subtype).Nondegenerate ∧
        (∀ c : C, i (0, c) = (c : V)) ∧
        ∀ (x : Fin m → k × k) (c : C),
          i (x, c) ∈ T ↔ x ∈ firstCoordinates k m ∧ c = 0) ∧
      m ≤ r ∧
      ((∀ S : Submodule k V, T ≤ S → totallyIsotropic q S → S = T) → m = r)) ∧
    ∃ T : Submodule k V, totallyIsotropic q T ∧ Module.finrank k T = r

end Specs.Alg01SymmetricWitt.Witt.WittIndexSubspaces
