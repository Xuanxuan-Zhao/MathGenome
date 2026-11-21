import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.UnitarityPairing
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Independent statements for paper.tex 1495–1522. The representative spaces
are left ideals in the regular module. Thus they have the inherited algebra
action, and all the displayed equivalences are actual group-algebra-linear
maps. No dimension hypothesis enters `Exhaustive` or `finiteDimensionalType`.
Finite products in the inner summands realize finite direct sums. -/
noncomputable section
universe u v w
namespace P103.Ch08.RegularMultiplicitySpecs
open scoped MonoidAlgebra

variable {G : Type u} [Group G]

/-- The representation on a left ideal of the regular module. -/
def idealRepresentation (S : Submodule ℂ[G] ℂ[G]) : Representation ℂ G S :=
  Representation.ofModule' S

/-- A finite list of candidate representatives, on their actual algebra modules. -/
structure Family (G : Type u) [Group G] where
  n : ℕ
  space : Fin n → Submodule ℂ[G] ℂ[G]

/-- Simplicity includes nonzeroness. Distinct indices have distinct types. -/
def Valid (C : Family G) : Prop :=
  (∀ i, IsSimpleModule ℂ[G] (C.space i)) ∧
  ∀ i j, Nonempty (C.space i ≃ₗ[ℂ[G]] C.space j) → i = j

/-- Every irreducible representation occurs, even in the absence of a prior
finite-dimensionality hypothesis. `V` may lie in a different universe. -/
def Exhaustive (C : Family G) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Irreducible ℂ G V ρ →
      ∃ i, Nonempty ((idealRepresentation (C.space i)).Equiv ρ)

/-- An actual direct-sum decomposition with the indicated natural multiplicities. -/
def Decomposition (C : Family G) {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (m : Fin C.n → ℕ) : Prop :=
  Nonempty (ρ.asModule ≃ₗ[ℂ[G]] Π₀ i : Fin C.n, (Fin (m i) → C.space i))

/-- The nonnegative integer multiplicity. The theorems below identify this
with the number of copies in an actual decomposition, not just a Hom dimension. -/
def multiplicity (C : Family G) {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (i : Fin C.n) : ℕ :=
  Module.finrank ℂ ((idealRepresentation (C.space i)).IntertwiningMap ρ)

def finiteDimensionalType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Irreducible ℂ G V ρ → FiniteDimensional ℂ V

def finiteFamilyType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G],
    ∃ C : Family G, Valid C ∧ Exhaustive.{u,v} C

/-- For any complete list without repetitions, the regular multiplicities
are the dimensions of those same representatives. -/
def regularDecompositionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family G),
    Valid C → Exhaustive.{u,u} C →
    Nonempty (ℂ[G] ≃ₗ[ℂ[G]]
      Π₀ i : Fin C.n, (Fin (Module.finrank ℂ (C.space i)) → C.space i)) ∧
    Fintype.card G = ∑ i : Fin C.n, (Module.finrank ℂ (C.space i)) ^ 2

/-- Existence of the decomposition for every finite-dimensional representation,
and identification of the count in every such decomposition with the pairing.
This includes zero multiplicities and the zero representation. -/
def multiplicityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family G),
    Valid C → Exhaustive.{u,v} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V),
      Decomposition C ρ (multiplicity C ρ) ∧
      ∀ (m : Fin C.n → ℕ), Decomposition C ρ m → ∀ i,
        (m i : ℂ) = UnitaritySpecs.functionPairingValue
          (CharacterSpecs.characterValue ρ)
          (CharacterSpecs.characterValue (idealRepresentation (C.space i)))

def characterClassificationType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    Nonempty (ρ.Equiv σ) ↔
      CharacterSpecs.characterValue ρ = CharacterSpecs.characterValue σ

end P103.Ch08.RegularMultiplicitySpecs
