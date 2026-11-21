import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Lemma 4.6 of paper.tex (characters of a finite abelian group).
The dual is the full group of homomorphisms into the complex unit circle. -/
noncomputable section
open scoped BigOperators

namespace P203Specs.FiniteCharacters

abbrev Dual (G : Type*) [CommGroup G] := G →* Circle

/-- A library equivalence supplies the enumeration used in the finite sums. -/
noncomputable def dualEquiv (G : Type*) [CommGroup G] [Finite G] : Dual G ≃* G :=
  (toUnits.monoidHomCongrRight (M := G)).trans
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G Circle).some

instance dualFinite (G : Type*) [CommGroup G] [Finite G] : Finite (Dual G) :=
  Finite.of_equiv G (dualEquiv G).symm.toEquiv

noncomputable instance dualFintype (G : Type*) [CommGroup G] [Finite G] : Fintype (Dual G) :=
  Fintype.ofFinite _

def finitenessType : Prop :=
  ∀ (G : Type*) [CommGroup G] [Finite G], Finite (Dual G)

def cardinalityType : Prop :=
  ∀ (G : Type*) [CommGroup G] [Fintype G], Nat.card (Dual G) = Fintype.card G

def averageType : Prop := by
  classical
  exact ∀ (G : Type*) [CommGroup G] [Fintype G] (g : G),
    (1 / (Fintype.card G : ℂ)) * ∑ χ : Dual G, (χ g : ℂ) =
      if g = 1 then 1 else 0

def nontrivialSumType : Prop :=
  ∀ (G : Type*) [CommGroup G] [Fintype G] (χ : Dual G), χ ≠ 1 →
    ∑ g : G, (χ g : ℂ) = 0

def valuesType : Prop :=
  ∀ (G : Type*) [CommGroup G] [Fintype G] (g : G) (ω : ℂ),
    (∃ χ : Dual G, (χ g : ℂ) = ω) ↔ ω ^ orderOf g = 1

def multiplicityType : Prop :=
  ∀ (G : Type*) [CommGroup G] [Fintype G] (g : G) (ω : ℂ),
    ω ^ orderOf g = 1 →
    Nat.card {χ : Dual G // (χ g : ℂ) = ω} = Fintype.card G / orderOf g

end P203Specs.FiniteCharacters
