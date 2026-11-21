import Mathlib.Combinatorics.SetFamily.Compression.UV
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Logic.Relation

namespace P205.Families.Shifting

abbrev Family (n : ℕ) := Finset (Finset (Fin n))

/-- The canonical singleton UV-compression, with the source's absent-image rule. -/
def shift {n : ℕ} (i j : Fin n) (F : Family n) : Family n :=
  UV.compression {i} {j} F

/-- The sum of the (zero-based) point labels over all members. Adding one to
all labels gives the source's one-based measure and the same decrease. -/
def labelSum {n : ℕ} (F : Family n) : ℕ := ∑ A ∈ F, ∑ a ∈ A, a.val

def Stable {n : ℕ} (F : Family n) : Prop := ∀ i j : Fin n, i < j → shift i j F = F

/-- Only shifts that change the family are legal steps. -/
def Step {n : ℕ} (F G : Family n) : Prop :=
  ∃ i j : Fin n, i < j ∧ shift i j F ≠ F ∧ G = shift i j F

/-- A finite sequence of legal shifts, including the empty sequence. -/
abbrev Steps {n : ℕ} := Relation.ReflTransGen (@Step n)

namespace Expected

def shiftRule : Prop := ∀ {n : ℕ} (i j : Fin n) (_hij : i ≠ j) (A : Finset (Fin n)),
  UV.compress ({i} : Finset (Fin n)) {j} A =
    if i ∉ A ∧ j ∈ A then insert i (A.erase j) else A

def cardinality : Prop := ∀ {n : ℕ} (i j : Fin n) (F : Family n),
  (shift i j F).card = F.card

def rank : Prop := ∀ {n k : ℕ} (i j : Fin n) (F : Family n),
  (F : Set (Finset (Fin n))).Sized k →
  (shift i j F : Set (Finset (Fin n))).Sized k

def intersection : Prop := ∀ {n : ℕ} (i j : Fin n) (_hij : i < j) (F : Family n),
  (F : Set (Finset (Fin n))).Intersecting →
  (shift i j F : Set (Finset (Fin n))).Intersecting

def decrease : Prop := ∀ {n : ℕ} (i j : Fin n) (_hij : i < j) (F : Family n),
  shift i j F ≠ F → labelSum (shift i j F) < labelSum F

def termination : Prop := ∀ n : ℕ, WellFounded (fun G F : Family n => Step F G)

def reachableStable : Prop := ∀ {n : ℕ} (F : Family n),
  ∃ G : Family n, Steps F G ∧ Stable G

def normalForm : Prop := ∀ {n k : ℕ} (F : Family n),
  (F : Set (Finset (Fin n))).Sized k →
  (F : Set (Finset (Fin n))).Intersecting →
  ∃ G : Family n, Steps F G ∧ Stable G ∧ G.card = F.card ∧
    (G : Set (Finset (Fin n))).Sized k ∧
    (G : Set (Finset (Fin n))).Intersecting

end Expected
end P205.Families.Shifting
