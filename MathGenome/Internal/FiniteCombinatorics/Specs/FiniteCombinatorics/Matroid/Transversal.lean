import Mathlib.Basic.Finite.Sum
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Foundations

/-! W76: arbitrary finite sides of a bipartite relation.  The ambient types
need not be finite.  An independent set has an injective choice into the
specified right side; the matching formulation has exactly that left support. -/

universe u v
noncomputable section
namespace FiniteCombinatorics.Matroid.Transversal
open Set
variable {α : Type u} {β : Type v}

def Matchable (R : Set β) (Rel : α → β → Prop) (I : Set α) : Prop :=
  ∃ f : I → R, Function.Injective f ∧ ∀ i : I, Rel i.val (f i)

def ChoiceIndependent (E : Set α) (R : Set β) (Rel : α → β → Prop)
    (I : Set α) : Prop := I ⊆ E ∧ Matchable R Rel I

/-- Distinct tagged copies keep the two sides disjoint even when α = β. -/
def bipartiteGraph (E : Set α) (R : Set β) (Rel : α → β → Prop) :
    SimpleGraph (E ⊕ R) where
  Adj
    | .inl e, .inr r => Rel e r
    | .inr r, .inl e => Rel e r
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def MatchingIndependent (E : Set α) (R : Set β) [Finite E] [Finite R]
    (Rel : α → β → Prop) (I : Set α) : Prop :=
  I ⊆ E ∧ ∃ M : Set (Sym2 (E ⊕ R)),
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsMatchingValue
      (bipartiteGraph E R Rel) M ∧
    ∀ e : E, Specs.FiniteCombinatorics.Graph.Matching.Foundations.SaturatedValue
      M (Sum.inl e) ↔ e.val ∈ I

/-- Saturation allows other left vertices to be matched as well. -/
def Saturable (E : Set α) (R : Set β) [Finite E] [Finite R]
    (Rel : α → β → Prop) (I : Set α) : Prop :=
  I ⊆ E ∧ ∃ M : Set (Sym2 (E ⊕ R)),
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsMatchingValue
      (bipartiteGraph E R Rel) M ∧
    ∀ e : E, e.val ∈ I →
      Specs.FiniteCombinatorics.Graph.Matching.Foundations.SaturatedValue M (Sum.inl e)

end FiniteCombinatorics.Matroid.Transversal

namespace Specs.FiniteCombinatorics.Matroid.Transversal
open Set _root_.FiniteCombinatorics.Matroid.Transversal
variable {α : Type u} {β : Type v}

def empty_matchableType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (R : Set β) (Rel : α → β → Prop), Matchable R Rel ∅

def matchable_subsetType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (R : Set β) (Rel : α → β → Prop) (I J : Set α),
    Matchable R Rel J → I ⊆ J → Matchable R Rel I

def matchable_augmentationType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (R : Set β) (Rel : α → β → Prop) (I J : Set α),
    I.Finite → J.Finite → Matchable R Rel I → Matchable R Rel J →
    I.ncard < J.ncard → ∃ e ∈ J \ I, Matchable R Rel (insert e I)

def choice_iff_matchingType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (E : Set α) (R : Set β) [Finite E] [Finite R]
    (Rel : α → β → Prop) (I : Set α),
    ChoiceIndependent E R Rel I ↔ MatchingIndependent E R Rel I

def choice_iff_saturationType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (E : Set α) (R : Set β) [Finite E] [Finite R]
    (Rel : α → β → Prop) (I : Set α),
    ChoiceIndependent E R Rel I ↔ Saturable E R Rel I

def transversal_matroidType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (E : Set α) (R : Set β) (Rel : α → β → Prop), E.Finite → R.Finite →
    ∃! M : _root_.Matroid α, M.E = E ∧
      ∀ I, M.Indep I ↔ ChoiceIndependent E R Rel I

def transversal_matroid_matchingType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (E : Set α) (R : Set β) [Finite E] [Finite R] (Rel : α → β → Prop),
    ∃! M : _root_.Matroid α, M.E = E ∧
      ∀ I, M.Indep I ↔ Saturable E R Rel I

def empty_leftType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (R : Set β) (Rel : α → β → Prop) (I : Set α),
    ChoiceIndependent ∅ R Rel I ↔ I = ∅

/-- No right vertices, or no edges at all, permits only the empty independent set. -/
def empty_rightType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (Rel : α → β → Prop) (I : Set α), Matchable ∅ Rel I ↔ I = ∅

def isolated_not_independentType : Prop :=
  ∀ {α : Type u} {β : Type v},
  ∀ (E : Set α) (R : Set β) (Rel : α → β → Prop) (e : α),
    (∀ r ∈ R, ¬ Rel e r) → ¬ ChoiceIndependent E R Rel {e}

end Specs.FiniteCombinatorics.Matroid.Transversal
