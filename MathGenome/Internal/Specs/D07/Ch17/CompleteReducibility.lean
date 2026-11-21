import MathGenome.Internal.Specs.D07.Ch17.IrreducibleDefinitionFiniteSemisimpleDecomposition
import MathGenome.Internal.Specs.D07.Ch17.MaschkeProjection

/-!
Independent specification for K07.17.complete_reducibility,
paper.tex:4852–4861. The group is finite and its order is nonzero in the
field. Finite dimension is needed for the finite irreducible decomposition,
but not for semisimplicity. No algebraic closedness hypothesis is imposed.
The summands carry the restrictions of the original action. The external
sum equivalence is the canonical addition map, and the zero space admits
the empty sum.
-/
namespace Specs.D07.Ch17.CompleteReducibility

universe u v w

/-- Maschke's complement property, in the shared definition of semisimplicity. -/
def Semisimplicity : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [Finite G] [AddCommGroup V] [Module K V],
    (Nat.card G : K) ≠ 0 → ∀ ρ : Representation K G V,
      IrreducibleDefinitionFiniteSemisimpleDecomposition.HasInvariantComplements ρ

/-- A finite internal sum of nonzero irreducible invariant subspaces. -/
def InternalDecomposition : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [Finite G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    (Nat.card G : K) ≠ 0 → ∀ ρ : Representation K G V,
      ∃ (n : ℕ) (U : Fin n → Subrepresentation ρ),
        (∀ i, Representation.IsIrreducible (U i).toRepresentation) ∧
        DirectSum.IsInternal (fun i => (U i).toSubmodule)

/-- The external direct sum is equivariantly isomorphic to the original
representation, and its isomorphism sends coordinates to their sum. -/
def EquivariantDecomposition : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [Finite G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    (Nat.card G : K) ≠ 0 → ∀ ρ : Representation K G V,
      ∃ (n : ℕ) (U : Fin n → Subrepresentation ρ)
        (e : (Representation.directSum (fun i => (U i).toRepresentation)).Equiv ρ),
        (∀ i, Representation.IsIrreducible (U i).toRepresentation) ∧
        ∀ x, e x = DirectSum.coeLinearMap (fun i => (U i).toSubmodule) x

/-- The zero space has the empty internal and external decomposition.
This boundary case needs no restriction on the group or characteristic. -/
def EmptyDecomposition : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [Subsingleton V]
    (ρ : Representation K G V),
    ∃ (U : Fin 0 → Subrepresentation ρ)
      (e : (Representation.directSum (fun i => (U i).toRepresentation)).Equiv ρ),
      (∀ i, Representation.IsIrreducible (U i).toRepresentation) ∧
      DirectSum.IsInternal (fun i => (U i).toSubmodule) ∧
      ∀ x, e x = DirectSum.coeLinearMap (fun i => (U i).toSubmodule) x

end Specs.D07.Ch17.CompleteReducibility
