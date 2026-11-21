import MathGenome.Internal.Specs.D07.Ch17.DirectSums
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The finite-dimensional semisimplicity theorem, paper.tex:4727–4777.
All groups and fields are allowed. Internal direct sums use the actual bijective
addition map from the finitely supported sum. An atom is a nonzero invariant
subspace with no smaller nonzero invariant subspace; see AtomCharacterization.
-/
namespace Specs.D07.Ch17.IrreducibleDefinitionFiniteSemisimpleDecomposition

universe u v w x

variable {K : Type u} {G : Type v} {V : Type w}
  [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- The paper's complement property, with invariance bundled in the subspaces. -/
def HasInvariantComplements (ρ : Representation K G V) : Prop :=
  ∀ U : Subrepresentation ρ, ∃ W : Subrepresentation ρ,
    IsCompl U.toSubmodule W.toSubmodule

/-- A finite internal sum of nonzero irreducible invariant subspaces.
`Fin 0` permits the empty decomposition of the zero space. -/
def HasFiniteIrreducibleDecomposition (ρ : Representation K G V) : Prop :=
  ∃ (n : ℕ) (U : Fin n → Subrepresentation ρ),
    (∀ i, IsAtom (U i)) ∧ DirectSum.IsInternal (fun i => (U i).toSubmodule)

def FiniteSemisimpleDecomposition : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K G V),
    HasInvariantComplements ρ ↔ HasFiniteIrreducibleDecomposition ρ

/-- This identifies the irreducibles in the internal-sum statement with the
usual nonzero irreducible restriction representations, rather than assuming it. -/
def AtomCharacterization : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Subrepresentation ρ),
    (IsAtom U ↔ U ≠ ⊥ ∧ ∀ A : Subrepresentation ρ, A ≤ U → A = ⊥ ∨ A = U) ∧
    (IsAtom U ↔ Representation.IsIrreducible U.toRepresentation)

/-- The complement property passes to every invariant subspace, in particular
to each invariant direct summand, without a dimension assumption. -/
def Inheritance : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V), HasInvariantComplements ρ →
    ∀ U : Subrepresentation ρ, HasInvariantComplements U.toRepresentation

/-- The graph case in the converse proof. In S × (B ⊕ C), the graph of an
equivariant f : B → S has invariant complement S × C. This includes nonzero
maps, and does not assume that the graph is a coordinate subspace. -/
def GraphComplement : Prop :=
  ∀ (K : Type u) (G : Type v) (S : Type w) (T : Type x)
    [Field K] [Group G] [AddCommGroup S] [AddCommGroup T]
    [Module K S] [Module K T]
    (ρ : Representation K G S) (σ : Representation K G T)
    (B C : Subrepresentation σ)
    (f : B.toSubmodule →ₗ[K] S),
    IsCompl B.toSubmodule C.toSubmodule →
    B.toRepresentation.IsIntertwiningMap ρ f →
    let Γ := LinearMap.range (f.prod B.toSubmodule.subtype)
    let W := (⊤ : Submodule K S).prod C.toSubmodule
    Specs.D07.Ch17.DirectSums.Invariant (ρ.prod σ) Γ ∧
    Specs.D07.Ch17.DirectSums.Invariant (ρ.prod σ) W ∧ IsCompl Γ W

/-- Every invariant subspace disjoint from the first coordinate is covered by
the graph case: project to T, complement its image there, and take S × C.
No graph presentation is imposed as an additional assumption. -/
def GraphCaseComplement : Prop :=
  ∀ (K : Type u) (G : Type v) (S : Type w) (T : Type x)
    [Field K] [Group G] [AddCommGroup S] [AddCommGroup T]
    [Module K S] [Module K T]
    (ρ : Representation K G S) (σ : Representation K G T)
    (A : Subrepresentation (ρ.prod σ)),
    HasInvariantComplements σ →
    Disjoint A.toSubmodule ((⊤ : Submodule K S).prod (⊥ : Submodule K T)) →
    ∃ C : Subrepresentation σ,
      Specs.D07.Ch17.DirectSums.Invariant (ρ.prod σ)
        ((⊤ : Submodule K S).prod C.toSubmodule) ∧
      IsCompl A.toSubmodule ((⊤ : Submodule K S).prod C.toSubmodule)

/-- The zero space has the empty internal sum, and has invariant complements. -/
def ZeroSpace : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [Subsingleton V] (ρ : Representation K G V),
    HasInvariantComplements ρ ∧
    ∃ U : Fin 0 → Subrepresentation ρ,
      (∀ i, IsAtom (U i)) ∧ DirectSum.IsInternal (fun i => (U i).toSubmodule)

/-- The canonical addition is an equivalence of representations, supplying the
external direct-sum formulation as well as the internal one. -/
def EquivariantDecomposition : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K G V),
    HasInvariantComplements ρ →
    ∃ (n : ℕ) (U : Fin n → Subrepresentation ρ)
      (e : (Representation.directSum (fun i => (U i).toRepresentation)).Equiv ρ),
      (∀ i, Representation.IsIrreducible (U i).toRepresentation) ∧
      ∀ x, e x = DirectSum.coeLinearMap (fun i => (U i).toSubmodule) x

end Specs.D07.Ch17.IrreducibleDefinitionFiniteSemisimpleDecomposition
