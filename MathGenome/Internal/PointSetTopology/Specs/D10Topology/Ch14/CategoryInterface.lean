import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.TopologicalFoundations
import Mathlib.Topology.GDelta.Basic

/-! Independent ambient-set specification of paper.tex 14.1–14.2.
All interiors, closures, complements and density statements use the specified
topology on X; no separation or nonemptiness hypothesis is imposed.
Countable families include the empty family. -/

open Set
universe u

namespace Specs.D10Topology.Ch14.CategoryInterface

def ambientSetPredicateType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → Set X → Prop

def nowhereDenseValue : ambientSetPredicateType :=
  fun A => interior (closure A) = ∅

def meagerValue : ambientSetPredicateType := fun A =>
  ∃ S : Set (Set _), S.Countable ∧ (∀ B ∈ S, nowhereDenseValue B) ∧ A = ⋃₀ S

def residualValue : ambientSetPredicateType := fun A => meagerValue Aᶜ

def secondCategoryValue : ambientSetPredicateType := fun A => ¬ meagerValue A

def baireType : Type (u + 1) := (X : Type u) → [TopologicalSpace X] → Prop

def baireValue : baireType := fun X _ =>
  ∀ S : Set (Set X), S.Countable →
    (∀ U ∈ S, IsOpen U ∧ Dense U) → Dense (⋂₀ S)

def nowhereDense_iff_library : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    nowhereDenseValue A ↔ IsNowhereDense A

def meager_iff_library : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    meagerValue A ↔ IsMeagre A

def residual_iff_library : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    residualValue A ↔ A ∈ residual X

def secondCategory_iff_library : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    secondCategoryValue A ↔ ¬ IsMeagre A

def baire_iff_library : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], baireValue X ↔ BaireSpace X

def empty_baire : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], baireValue X

def baire_iff_no_open_meager : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    baireValue X ↔ ∀ U : Set X, IsOpen U → U.Nonempty → ¬ meagerValue U

def baire_iff_closed_unions : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    baireValue X ↔ ∀ F : Set (Set X), F.Countable →
      (∀ C ∈ F, IsClosed C ∧ interior C = ∅) → interior (⋃₀ F) = ∅

def baire_iff_residual_dense : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    baireValue X ↔ ∀ R : Set X, residualValue R → Dense R

def residual_contains_intersection : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (R : Set X), residualValue R →
    ∃ S : Set (Set X), S.Countable ∧ (∀ U ∈ S, IsOpen U ∧ Dense U) ∧
      ⋂₀ S ⊆ R ∧ IsGδ (⋂₀ S) ∧ (baireValue X → Dense (⋂₀ S))

def contains_dense_gdelta_residual : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (R G : Set X),
    G ⊆ R → IsGδ G → Dense G → residualValue R

def residual_iff_contains_dense_gdelta : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], baireValue X → ∀ R : Set X,
    residualValue R ↔ ∃ G : Set X, G ⊆ R ∧ IsGδ G ∧ Dense G

end Specs.D10Topology.Ch14.CategoryInterface
