import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Duality

/-! Independent statements for the operation laws in paper.tex, W69.
The rank formulas and the basis criterion are allocated to MinorRank.
The canonical operations ignore elements outside the current ground, so these
statements hold for all ambient sets, in particular for subsets of the original
finite ground as in the source. No ground or operation set must be nonempty. -/

namespace FiniteCombinatorics.Matroid.Expected

open Set
open scoped _root_.Matroid
universe u

def successiveDeletions : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C D : Set α),
    (M ＼ C) ＼ D = M ＼ (C ∪ D)

def successiveContractions : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C D : Set α),
    (M ／ C) ／ D = M ／ (C ∪ D)

def disjointDeletionContraction : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C D : Set α),
    Disjoint C D → (M ／ C) ＼ D = (M ＼ D) ／ C

def emptyDeletion : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite], M ＼ ∅ = M

def emptyContraction : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite], M ／ ∅ = M

/-- Intersecting the second deletion with its current ground changes nothing. -/
def deletionCurrentGround : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C D : Set α),
    (M ＼ C) ＼ (D ∩ (M ＼ C).E) = (M ＼ C) ＼ D

/-- Intersecting the second contraction with its current ground changes nothing. -/
def contractionCurrentGround : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C D : Set α),
    (M ／ C) ／ (D ∩ (M ／ C).E) = (M ／ C) ／ D

def successiveDeletionsGround : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C D : Set α),
    ((M ＼ C) ＼ D).E = M.E \ (C ∪ D)

def successiveContractionsGround : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C D : Set α),
    ((M ／ C) ／ D).E = M.E \ (C ∪ D)

/-- Both orders have the stated relative ground, even without disjointness. -/
def mixedMinorGround : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C D : Set α),
    ((M ／ C) ＼ D).E = M.E \ (C ∪ D) ∧
      ((M ＼ D) ／ C).E = M.E \ (C ∪ D)

end FiniteCombinatorics.Matroid.Expected
