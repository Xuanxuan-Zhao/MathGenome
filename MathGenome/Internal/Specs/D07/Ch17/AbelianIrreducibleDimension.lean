import MathGenome.Internal.Specs.D07.Ch17.SchurScalar

/-!
Independent specification of K07.17.abelian_irreducible_dimension,
paper.tex:4884–4895. Irreducibility is the shared nonzero notion.
The abelian group is arbitrary; there is no group cardinality or
characteristic restriction. The real rotation and modular failure of
semisimplicity are the previously allocated examples, not extra hypotheses.
-/
namespace Specs.D07.Ch17.AbelianIrreducibleDimension

universe u v w

/-- Each action operator is a uniquely determined scalar operator. -/
def ScalarAction : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [CommGroup G] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] (ρ : Representation K G V),
    Representation.IsIrreducible ρ →
    ∀ g : G, ∃! a : K, ρ g = a • (1 : Module.End K V)

/-- Scalar action makes the span of any vector invariant. -/
def LineInvariant : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [CommGroup G] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] (ρ : Representation K G V),
    Representation.IsIrreducible ρ → ∀ v : V,
    DirectSums.Invariant ρ (Submodule.span K {v})

/-- Every nonzero vector spans the entire irreducible space. -/
def LineSpans : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [CommGroup G] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] (ρ : Representation K G V),
    Representation.IsIrreducible ρ → ∀ v : V, v ≠ 0 →
    Submodule.span K {v} = ⊤

/-- An irreducible finite-dimensional representation of an abelian group
over an algebraically closed field has dimension one. -/
def DimensionOne : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [CommGroup G] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] (ρ : Representation K G V),
    Representation.IsIrreducible ρ → Module.finrank K V = 1

end Specs.D07.Ch17.AbelianIrreducibleDimension
