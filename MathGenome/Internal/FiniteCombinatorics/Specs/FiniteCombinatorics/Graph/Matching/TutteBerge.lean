import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Tutte
import Mathlib.Data.Finset.Max

/-! Independent statements for paper.tex W54. All extrema range over actual finite
sets or matchings. In particular each deficit is an integer difference. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Matching.TutteBerge
open Specs.FiniteCombinatorics.Graph.Matching.Foundations
open Specs.FiniteCombinatorics.Graph.Matching.Tutte

def deficitType := ∀ {V : Type u} [Finite V], SimpleGraph V → Set V → ℤ

def deficitValue : deficitType := fun {_} _ G S =>
  (oddComponentCountValue (deletedGraphValue G S) : ℤ) - (Nat.card S : ℤ)

def deficiencyType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℤ

def deficiencyValue : deficiencyType := fun {V} _ G =>
  letI := Fintype.ofFinite (Set V)
  Finset.univ.sup' Finset.univ_nonempty (deficitValue G)

def unmatchedCountType := ∀ {V : Type u} [Finite V], Set (Sym2 V) → ℕ

def unmatchedCountValue : unmatchedCountType := fun {V} _ M =>
  Nat.card {v : V // ¬ SaturatedValue M v}

/-- The empty matching makes the optimization domain nonempty, including V empty. -/
def emptyEdgeMatching {V : Type u} [Finite V] (G : SimpleGraph V) : EdgeMatchingValue G :=
  ⟨∅, Set.empty_subset _ , fun _ h => False.elim h⟩

instance {V : Type u} [Finite V] (G : SimpleGraph V) : Finite (EdgeMatchingValue G) :=
  inferInstanceAs (Finite {M : Set (Sym2 V) // IsMatchingValue G M})

def minimumUnmatchedType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ

def minimumUnmatchedValue : minimumUnmatchedType := fun {_} _ G =>
  letI := Fintype.ofFinite (EdgeMatchingValue G)
  letI : Nonempty (EdgeMatchingValue G) := ⟨emptyEdgeMatching G⟩
  Finset.univ.inf' Finset.univ_nonempty (fun M : EdgeMatchingValue G => unmatchedCountValue M.val)

def maximumMatchingSizeType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ

def maximumMatchingSizeValue : maximumMatchingSizeType := fun {_} _ G =>
  letI := Fintype.ofFinite (EdgeMatchingValue G)
  letI : Nonempty (EdgeMatchingValue G) := ⟨emptyEdgeMatching G⟩
  Finset.univ.sup' Finset.univ_nonempty (fun M : EdgeMatchingValue G => Nat.card M.val)

def tutteBergeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    0 ≤ deficiencyValue G ∧
    (minimumUnmatchedValue G : ℤ) = deficiencyValue G ∧
    (maximumMatchingSizeValue G : ℤ) = ((Nat.card V : ℤ) - deficiencyValue G) / 2 ∧
    2 * (maximumMatchingSizeValue G : ℤ) + deficiencyValue G = (Nat.card V : ℤ) ∧
    deficiencyValue G % 2 = (Nat.card V : ℤ) % 2

def empty_tutteBergeType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] (G : SimpleGraph V),
    deficiencyValue G = 0 ∧ minimumUnmatchedValue G = 0 ∧ maximumMatchingSizeValue G = 0

end Specs.FiniteCombinatorics.Graph.Matching.TutteBerge
