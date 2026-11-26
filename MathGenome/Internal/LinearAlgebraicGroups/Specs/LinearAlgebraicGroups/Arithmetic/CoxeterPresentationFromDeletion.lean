import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace LinearAlgebraicGroups.Specs.CoxeterPresentationFromDeletion

/-- Evaluation of a word in the given generating family. -/
def wordValue {S W : Type*} [Group W] (s : S → W) (l : List S) : W :=
  (l.map s).prod

/-- A word admitting a shorter representative admits deletion of two letters. -/
def DeletionCondition {S W : Type*} [Group W] (s : S → W) : Prop :=
  ∀ l : List S, (∃ k : List S, wordValue s k = wordValue s l ∧ k.length < l.length) →
    ∃ (p m q : List S) (i j : S),
      l = p ++ i :: (m ++ j :: q) ∧ wordValue s (p ++ m ++ q) = wordValue s l

/-- Deletion recognizes the Coxeter presentation on the given generators.
An entry is zero when the corresponding product has infinite order. -/
def PresentationFromDeletion.{u,v} : Prop :=
  ∀ {S : Type u} {W : Type v} [Group W] (s : S → W),
    Function.Injective s → (∀ i, s i ≠ 1) → (∀ i, s i * s i = 1) →
    Subgroup.closure (Set.range s) = ⊤ → DeletionCondition s →
    ∃ M : CoxeterMatrix S, (∀ i j, M i j = orderOf (s i * s j)) ∧
      ∃ cs : CoxeterSystem M W, cs.simple = s

end LinearAlgebraicGroups.Specs.CoxeterPresentationFromDeletion
