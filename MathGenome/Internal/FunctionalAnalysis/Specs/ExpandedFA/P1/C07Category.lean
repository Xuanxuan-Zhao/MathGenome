import Mathlib.Topology.GDelta.Basic

/-!
Independent specification of Definition `fa2:p1:c07:category` (paper.tex, 1366–1372).
The canonical objects are Mathlib's `IsNowhereDense`, `IsMeagre`, and
`BaireSpace`. The propositions below specify their meanings without assuming
any metric, completeness, separation, or nonemptiness hypothesis.
-/

open Set TopologicalSpace

universe u

namespace Specs.ExpandedFA.P1.C07Category

/-- Type and canonical value of the nowhere-dense predicate. -/
def nowhereDenseType : Type (u + 1) :=
  ∀ {X : Type u}, [TopologicalSpace X] → Set X → Prop

def nowhereDenseValue : nowhereDenseType :=
  fun A => interior (closure A) = ∅

/-- Mathlib's meagre predicate, identified with the source by `meagreMeaning`. -/
def meagreType : Type (u + 1) :=
  ∀ {X : Type u}, [TopologicalSpace X] → Set X → Prop

def meagreValue : meagreType := @IsMeagre

/-- Mathlib's Baire predicate, identified with the source below. -/
def baireType : Type (u + 1) :=
  ∀ (X : Type u), [TopologicalSpace X] → Prop

def baireValue : baireType := BaireSpace

/-- A nowhere dense set has closure with empty interior. -/
def nowhereDenseMeaning : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    IsNowhereDense A ↔ interior (closure A) = ∅

/-- An exact countable union, with the empty family permitted. -/
def meagreMeaning : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    IsMeagre A ↔ ∃ S : Set (Set X),
      S.Countable ∧ (∀ B ∈ S, interior (closure B) = ∅) ∧ A = ⋃₀ S

/-- The natural-number formulation used by the canonical class. -/
def baireNatMeaning : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    BaireSpace X ↔ ∀ G : ℕ → Set X,
      (∀ n, IsOpen (G n)) → (∀ n, Dense (G n)) → Dense (⋂ n, G n)

/-- Every countable family, including finite and empty families. -/
def baireMeaning : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    BaireSpace X ↔ ∀ S : Set (Set X),
      S.Countable → (∀ G ∈ S, IsOpen G) → (∀ G ∈ S, Dense G) → Dense (⋂₀ S)

def emptyNowhereDense : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], IsNowhereDense (∅ : Set X)

def emptyMeagre : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], IsMeagre (∅ : Set X)

def emptySpaceBaire : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], BaireSpace X

end Specs.ExpandedFA.P1.C07Category
