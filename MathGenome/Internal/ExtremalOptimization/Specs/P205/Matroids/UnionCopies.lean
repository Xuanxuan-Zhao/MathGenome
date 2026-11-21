import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Models
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Data.Set.Card.Arithmetic

/-! Labelled copies for paper.tex, 2396–2409.  The ambient type is arbitrary;
only the specified common ground is finite. All constructions allow `k = 0`. -/
namespace P205.Matroids
open Set
universe u

abbrev CopyGround {α : Type u} (S : Set α) (k : ℕ) := S × Fin k

/-- The subtype-valued slice of a set of labelled copies. -/
def copyFiber {α : Type u} {S : Set α} {k : ℕ}
    (J : Set (CopyGround S k)) (i : Fin k) : Set S := {e | (e, i) ∈ J}

/-- A slice regarded as a subset of the original ambient type. -/
def copySlice {α : Type u} {S : Set α} {k : ℕ}
    (J : Set (CopyGround S k)) (i : Fin k) : Set α := Subtype.val '' copyFiber J i

/-- Original elements represented by a set of copies. -/
def copyLabels {α : Type u} {S : Set α} {k : ℕ}
    (J : Set (CopyGround S k)) : Set α := (fun p => (p.1 : α)) '' J

/-- Label every element of part `i` by `i`. -/
def labelledParts {α : Type u} (S : Set α) {k : ℕ}
    (parts : Fin k → Set α) : Set (CopyGround S k) := {p | (p.1 : α) ∈ parts p.2}

/-- An actual disjoint assignment of precisely `I`, inside `S`. -/
def DisjointAssignment {α : Type u} {k : ℕ} (F : Family α k)
    (S I : Set α) (parts : Fin k → Set α) : Prop :=
  I ⊆ S ∧ (∀ i, (F.matroid i).Indep (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧ I = ⋃ i, parts i

end P205.Matroids

namespace Specs.P205.Matroids
open _root_.P205.Matroids Set
open scoped BigOperators
noncomputable section
universe u

def sliceMatroidType := ∀ {α : Type u} {k : ℕ}, Family α k →
  (S : Set α) → Matroid (CopyGround S k)

def sliceMatroidValue : sliceMatroidType.{u} := fun F S =>
  (Matroid.sum' (fun i => (F.matroid i).restrictSubtype S)).comap Prod.swap

def labelMatroidType := ∀ {α : Type u} (S : Set α) (k : ℕ), Matroid (CopyGround S k)

def labelMatroidValue : labelMatroidType.{u} := fun {α} S k =>
  (Matroid.freeOn S).comap (fun p : CopyGround S k => (p.1 : α))

def SliceGround : Prop := ∀ {α : Type u} {k : ℕ} (F : Family α k) (S : Set α),
  (sliceMatroidValue F S).E = univ

def LabelGround : Prop := ∀ {α : Type u} (S : Set α) (k : ℕ),
  (labelMatroidValue S k).E = univ

def CopyFinite : Prop := ∀ {α : Type u} {k : ℕ} (F : Family α k) (S : Set α),
  S ⊆ F.ground → (sliceMatroidValue F S).Finite ∧ (labelMatroidValue S k).Finite

def SliceIndep : Prop := ∀ {α : Type u} {k : ℕ} (F : Family α k) (S : Set α)
  (J : Set (CopyGround S k)),
  (sliceMatroidValue F S).Indep J ↔ ∀ i, (F.matroid i).Indep (copySlice J i)

def LabelIndep : Prop := ∀ {α : Type u} (S : Set α) (k : ℕ)
  (J : Set (CopyGround S k)),
  (labelMatroidValue S k).Indep J ↔ J.InjOn (fun p => (p.1 : α))

def SliceRank : Prop := ∀ {α : Type u} {k : ℕ} (F : Family α k) (S : Set α),
  S ⊆ F.ground → ∀ U : Set (CopyGround S k),
  rankValue (sliceMatroidValue F S) U = ∑ i, rankValue (F.matroid i) (copySlice U i)

def LabelRank : Prop := ∀ {α : Type u} (S : Set α) (k : ℕ)
  (Y : Set (CopyGround S k)),
  rankValue (labelMatroidValue S k) Y = (copyLabels Y).ncard

def CommonAssignment : Prop := ∀ {α : Type u} {k : ℕ} (F : Family α k) (S : Set α)
  (J : Set (CopyGround S k)),
  ((sliceMatroidValue F S).Indep J ∧ (labelMatroidValue S k).Indep J) ↔
    DisjointAssignment F S (copyLabels J) (copySlice J)

def CommonCardinality : Prop := ∀ {α : Type u} {k : ℕ} (F : Family α k) (S : Set α)
  (J : Set (CopyGround S k)),
  (sliceMatroidValue F S).Indep J → (labelMatroidValue S k).Indep J →
  (copyLabels J).ncard = J.ncard

def AssignmentCopies : Prop := ∀ {α : Type u} {k : ℕ} (F : Family α k) (S I : Set α)
  (parts : Fin k → Set α), DisjointAssignment F S I parts →
    (sliceMatroidValue F S).Indep (labelledParts S parts) ∧
    (labelMatroidValue S k).Indep (labelledParts S parts) ∧
    copyLabels (labelledParts S parts) = I ∧
    (∀ i, copySlice (labelledParts S parts) i = parts i) ∧
    (labelledParts S parts).ncard = I.ncard

def CopiesInverse : Prop := ∀ {α : Type u} {S : Set α} {k : ℕ}
  (J : Set (CopyGround S k)), labelledParts S (copySlice J) = J

end
end Specs.P205.Matroids
