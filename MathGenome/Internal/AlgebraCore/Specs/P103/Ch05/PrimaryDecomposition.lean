import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimarySubmodules
import Mathlib.Data.Finset.Lattice.Fold

/-!
The decomposition and associated-radical assertions of Theorem 5.5,
paper.tex:997–1003,1012–1018. Finite families are finite sets of submodules.
Irredundancy explicitly says that deleting any component changes the
intersection. Primary submodules are proper by `primaryValue`.
The localization and second uniqueness assertions are allocated separately.
-/
namespace P103.Specs.Ch05.PrimaryDecomposition

universe u v
open P103.Specs.Ch05.PrimarySubmodules
open P103.Specs.Ch05.AssociatedPrimesInterface

/-- A finite nonempty irredundant primary decomposition with distinct
quotient-annihilator radicals, using the source's primary predicate. -/
structure IsDecomposition {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (N : Submodule R M)
    (s : Finset (Submodule R M)) : Prop where
  nonempty : s.Nonempty
  primary : ∀ Q ∈ s, primaryValue R M Q
  intersection : (⨅ Q ∈ s, Q) = N
  distinct : (s : Set (Submodule R M)).Pairwise
    (fun Q P => radicalValue R M Q ≠ radicalValue R M P)
  irredundant : ∀ Q ∈ s, (⨅ P ∈ s.erase Q, P) ≠ N

/-- No decomposition is supplied as a hypothesis. Properness alone gives
the nonempty family; in particular this applies to zero in a nonzero module. -/
def exists_decompositionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M), N ≠ ⊤ →
      ∃ s : Finset (Submodule R M), IsDecomposition N s

/-- This quantifies over every decomposition satisfying the stated
conditions, rather than just the family produced by existence. -/
def associatedPrimes_eq_radicalsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (s : Finset (Submodule R M)), IsDecomposition N s →
      associatedPrimesValue R (M ⧸ N) = (fun Q => radicalValue R M Q) '' (s : Set _)

end P103.Specs.Ch05.PrimaryDecomposition
