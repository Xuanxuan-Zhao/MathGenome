import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.GDelta.Basic

/-!
Independent specification of paper.tex, d10:07:axioms and the G_delta
terminology in d10:07:metric-normal. All predicates use the given canonical
topology. Regularity and normality have no implicit T1 hypothesis, and the
closed sets in the separation conditions may be empty.
-/

open Set
universe u

namespace Specs.D10Topology.Ch07.SeparationConventions

def separationType : Type (u + 1) := (X : Type u) → [t : TopologicalSpace X] → Prop
def t0Value (X : Type u) [TopologicalSpace X] : Prop := T0Space X
def t1Value (X : Type u) [TopologicalSpace X] : Prop := T1Space X
def t2Value (X : Type u) [TopologicalSpace X] : Prop := T2Space X
def regularValue (X : Type u) [TopologicalSpace X] : Prop := RegularSpace X
def normalValue (X : Type u) [TopologicalSpace X] : Prop := NormalSpace X
def t3Value (X : Type u) [TopologicalSpace X] : Prop := RegularSpace X ∧ T1Space X
def t4Value (X : Type u) [TopologicalSpace X] : Prop := NormalSpace X ∧ T1Space X
def completelyRegularValue (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (F : Set X), IsClosed F → ∀ x : X, x ∉ F →
    ∃ f : X → unitInterval, Continuous f ∧ f x = 1 ∧ ∀ y ∈ F, f y = 0
def tychonoffValue (X : Type u) [TopologicalSpace X] : Prop :=
  completelyRegularValue X ∧ T2Space X

def gdeltaType : Type (u + 1) :=
  {X : Type u} → [t : TopologicalSpace X] → Set X → Prop
def gdeltaValue {X : Type u} [TopologicalSpace X] (A : Set X) : Prop := IsGδ A

def t0_iff_open_distinguishes : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], t0Value X ↔
    ∀ x y : X, x ≠ y → ∃ U : Set X, IsOpen U ∧
      ((x ∈ U ∧ y ∉ U) ∨ (y ∈ U ∧ x ∉ U))

def t1_iff_closed_singletons : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], t1Value X ↔ ∀ x : X, IsClosed ({x} : Set X)

def t2_iff_disjoint_open : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], t2Value X ↔
    ∀ x y : X, x ≠ y → ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V

def regular_iff_disjoint_open : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], regularValue X ↔
    ∀ (F : Set X), IsClosed F → ∀ x : X, x ∉ F →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ F ⊆ V ∧ Disjoint U V

def normal_iff_disjoint_open : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], normalValue X ↔
    ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V

def t3_iff_mathlib : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], t3Value X ↔ T3Space X

def t4_iff_mathlib : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], t4Value X ↔ T4Space X

/-- The paper uses 1 at the point and 0 on F; Mathlib uses the reverse. -/
def completelyRegular_iff_mathlib : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    completelyRegularValue X ↔ CompletelyRegularSpace X

/-- Mathlib T35 is defined using T0, whereas the paper requires Hausdorff. -/
def tychonoff_iff_mathlib : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], tychonoffValue X ↔ T35Space X

def gdelta_iff_countable_open_intersection : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X), gdeltaValue A ↔
    ∃ U : Set (Set X), U.Countable ∧ (∀ V ∈ U, IsOpen V) ∧ A = ⋂₀ U

def gdelta_iff_sequence_open_intersection : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X), gdeltaValue A ↔
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ A = ⋂ n, U n

def empty_separation_axioms : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X],
    t0Value X ∧ t1Value X ∧ t2Value X ∧ regularValue X ∧ normalValue X ∧
      t3Value X ∧ t4Value X ∧ completelyRegularValue X ∧ tychonoffValue X

end Specs.D10Topology.Ch07.SeparationConventions
