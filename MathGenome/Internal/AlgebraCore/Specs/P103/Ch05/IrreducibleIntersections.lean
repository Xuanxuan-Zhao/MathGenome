import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Order.Irreducible

/-!
The first paragraph of the proof of Theorem 5.5 in paper.tex (line 1012).
Rings are commutative and unital; the zero ring and zero module are allowed.
The finite intersection is an infimum in the lattice of submodules, whose
empty infimum is the whole module. No primary decomposition is assumed.
-/

universe u v

namespace P103.Specs.Ch05.IrreducibleIntersections

/-- The source's definition, including properness. This canonical predicate
is shared by the specification and implementation. -/
def IsIrreducible {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (N : Submodule R M) : Prop :=
  N ≠ ⊤ ∧ ∀ A B : Submodule R M, N = A ⊓ B → N = A ∨ N = B

/-- Bridge to the library's order-theoretic irreducibility. -/
def irreducible_iff_infIrredType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M), IsIrreducible N ↔ InfIrred N

/-- Every submodule is a finite intersection of irreducible proper
submodules. The family is empty exactly when the submodule is the whole module. -/
def finite_intersectionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M),
    ∃ s : Finset (Submodule R M),
      (∀ Q ∈ s, IsIrreducible Q) ∧
      N = ⨅ Q ∈ s, Q ∧ (s = ∅ ↔ N = ⊤)

/-- A proper submodule has at least one irreducible component. -/
def proper_finite_intersectionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M), N ≠ ⊤ →
    ∃ s : Finset (Submodule R M), s.Nonempty ∧
      (∀ Q ∈ s, IsIrreducible Q) ∧ N = ⨅ Q ∈ s, Q

end P103.Specs.Ch05.IrreducibleIntersections
