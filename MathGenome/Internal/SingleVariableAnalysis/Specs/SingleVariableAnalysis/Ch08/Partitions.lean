import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Scalar
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Basic

/-! Independent interfaces for K03.08.partitions (paper.tex:1900).
The number of cells may be zero, precisely to include the degenerate interval.
All other partitions are finite strictly increasing endpoint lists. -/
namespace SingleVariableAnalysis.Riemann

structure PartitionData (a b : ℝ) where
  n : ℕ
  point : Fin (n + 1) → ℝ
  strictMono : StrictMono point
  first : point 0 = a
  last : point (Fin.last n) = b

end SingleVariableAnalysis.Riemann

namespace Specs.SingleVariableAnalysis.Ch08.Partitions
open _root_.SingleVariableAnalysis.Riemann
open scoped BigOperators
universe u

abbrev partitionType := ℝ → ℝ → Type
abbrev partitionValue : partitionType := PartitionData

noncomputable def pointsValue {a b : ℝ} (P : PartitionData a b) : Finset ℝ :=
  Finset.univ.image P.point
abbrev pointsType := {a b : ℝ} → PartitionData a b → Finset ℝ

def lengthValue {a b : ℝ} (P : PartitionData a b) (i : Fin P.n) : ℝ :=
  P.point i.succ - P.point i.castSucc
abbrev lengthType := {a b : ℝ} → (P : PartitionData a b) → Fin P.n → ℝ

noncomputable def meshValue {a b : ℝ} (P : PartitionData a b) : ℝ :=
  (insert 0 (Finset.univ.image (lengthValue P))).sup' (Finset.insert_nonempty _ _) id
abbrev meshType := {a b : ℝ} → PartitionData a b → ℝ

def taggingValue {a b : ℝ} (P : PartitionData a b) : Type :=
  ∀ i : Fin P.n, {x : ℝ // x ∈ Set.Icc (P.point i.castSucc) (P.point i.succ)}
abbrev taggingType := {a b : ℝ} → PartitionData a b → Type

noncomputable def sumValue {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {a b : ℝ} (P : PartitionData a b) (ξ : taggingValue P) (f : ℝ → E) : E :=
  ∑ i : Fin P.n, lengthValue P i • f (ξ i)
abbrev sumType := {E : Type u} → [AddCommMonoid E] → [Module ℝ E] →
  {a b : ℝ} → (P : PartitionData a b) → taggingValue P → (ℝ → E) → E

def refinesValue {a b : ℝ} (Q P : PartitionData a b) : Prop :=
  pointsValue P ⊆ pointsValue Q
abbrev refinesType := {a b : ℝ} → PartitionData a b → PartitionData a b → Prop

def endpoints : Prop := ∀ {a b : ℝ} (P : PartitionData a b),
  a ∈ pointsValue P ∧ b ∈ pointsValue P ∧ ∀ x ∈ pointsValue P, x ∈ Set.Icc a b

def cellPositive : Prop := ∀ {a b : ℝ} (P : PartitionData a b) (i : Fin P.n),
  0 < lengthValue P i

def meshMaximum : Prop := ∀ {a b : ℝ} (P : PartitionData a b),
  0 ≤ meshValue P ∧ (∀ i, lengthValue P i ≤ meshValue P) ∧
    (P.n ≠ 0 → ∃ i, meshValue P = lengthValue P i)

def tagsExist : Prop := ∀ {a b : ℝ} (P : PartitionData a b), Nonempty (taggingValue P)

def refinementLaws : Prop := ∀ {a b : ℝ} (P Q R : PartitionData a b),
  refinesValue P P ∧ (refinesValue R Q → refinesValue Q P → refinesValue R P)

def commonRefinement : Prop := ∀ {a b : ℝ} (P Q : PartitionData a b),
  ∃ R : PartitionData a b, pointsValue R = pointsValue P ∪ pointsValue Q ∧
    refinesValue R P ∧ refinesValue R Q

/-- Every finite set of points with exactly the required endpoints and bounds
has a strict ordered partition representation; no partitions are excluded. -/
def finiteRepresentation : Prop := ∀ {a b : ℝ} (s : Finset ℝ),
  a ∈ s → b ∈ s → (∀ x ∈ s, x ∈ Set.Icc a b) →
  ∃ P : PartitionData a b, pointsValue P = s

def uniformPartitions : Prop := ∀ {a b : ℝ}, a < b → ∀ n : ℕ, 0 < n →
  ∃ P : PartitionData a b, ∃ _hn : P.n = n,
    (∀ i : Fin (P.n + 1), P.point i = a + (i.val : ℝ) * (b-a) / n) ∧
    meshValue P = (b-a) / n

def arbitrarilyFine : Prop := ∀ {a b : ℝ}, a < b → ∀ ε : ℝ, 0 < ε →
  ∃ P : PartitionData a b, 0 < meshValue P ∧ meshValue P < ε

def degenerate : Prop := ∀ a : ℝ, ∃ P : PartitionData a a, P.n = 0 ∧
  meshValue P = 0 ∧ Nonempty (taggingValue P)

def degenerateAll : Prop := ∀ (a : ℝ) (P : PartitionData a a), P.n = 0 ∧ meshValue P = 0

def degenerateSum : Prop := ∀ {E : Type u} [AddCommMonoid E] [Module ℝ E]
  (a : ℝ) (P : PartitionData a a) (ξ : taggingValue P) (f : ℝ → E), sumValue P ξ f = 0

end Specs.SingleVariableAnalysis.Ch08.Partitions
