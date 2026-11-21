import MathGenome.Internal.Specs.D07.Ch21.GroupAlgebra
import MathGenome.Internal.Specs.D07.Ch17.CompleteReducibility
import MathGenome.Internal.Specs.D07.Ch17.SchurNonscalar
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Independent statements for the first paragraph of the proof of
K07.21.regular_decomposition, paper.tex:6340–6368. The target representation
is arbitrary dimensional. A complete family is represented by a finite set
of irreducible subrepresentations of the actual left regular representation.
Equivalence is the bundled equivariant linear equivalence, also across
different universes of representation spaces.
-/
namespace Specs.D07.Ch21.RegularDecompositionFiniteIrreducibleTypes

universe u v

/-- Evaluation at every nonzero vector is an equivariant quotient map,
with the source's explicit orbit-sum formula. -/
def CyclicQuotient : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Representation.IsIrreducible ρ → ∀ v : V, v ≠ 0 →
    ∃ q : MonoidAlgebra ℂ G →ₗ[ℂ] V,
      (∀ a, q a = ∑ g : G, a.coeff g • ρ g v) ∧
      (∀ g, q (MonoidAlgebra.single g 1) = ρ g v) ∧
      (Representation.leftRegular ℂ G).IsIntertwiningMap ρ q ∧
      Function.Surjective q

/-- Finite dimensionality is a conclusion, not an input to the bound. -/
def DimensionBound : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Representation.IsIrreducible ρ →
    Module.Finite ℂ V ∧ Module.finrank ℂ V ≤ Fintype.card G

/-- One finite irreducible decomposition of the regular representation
contains every irreducible type, without a dimension assumption on that type. -/
def RegularSummandsComplete : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∃ (n : ℕ) (U : Fin n → Subrepresentation (Representation.leftRegular ℂ G)),
      (∀ i, Representation.IsIrreducible (U i).toRepresentation) ∧
      DirectSum.IsInternal (fun i => (U i).toSubmodule) ∧
      ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
        Representation.IsIrreducible ρ →
        ∃ i, Nonempty ((U i).toRepresentation.Equiv ρ)

/-- A nonempty finite family of pairwise inequivalent irreducibles, universally
complete among all complex representations. The ambient regular space supplies
a fixed universe of representatives, so no size restriction is imposed on V. -/
def FiniteCompleteFamily : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∃ s : Finset (Subrepresentation (Representation.leftRegular ℂ G)),
      s.Nonempty ∧
      (∀ U ∈ s, Representation.IsIrreducible U.toRepresentation) ∧
      (s : Set (Subrepresentation (Representation.leftRegular ℂ G))).Pairwise
        (fun U W => ¬ Nonempty (U.toRepresentation.Equiv W.toRepresentation)) ∧
      ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
        Representation.IsIrreducible ρ →
        ∃ U ∈ s, Nonempty (U.toRepresentation.Equiv ρ)

/-- The one-element group has precisely its one-dimensional trivial type. -/
def TrivialGroupType : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G] [Subsingleton G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Representation.IsIrreducible ρ →
    Module.Finite ℂ V ∧ Module.finrank ℂ V = 1 ∧
      Nonempty (ρ.Equiv (Representation.trivial ℂ G ℂ))

end Specs.D07.Ch21.RegularDecompositionFiniteIrreducibleTypes
