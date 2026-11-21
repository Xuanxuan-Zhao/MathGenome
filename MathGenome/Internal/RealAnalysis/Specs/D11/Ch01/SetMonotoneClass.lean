import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.SetSystems

/-!
Independent statements for `paper.tex:422–441` (set monotone classes).
The definitions here are the shared objects used by the candidate. In particular,
monotone-class generation is defined by its intersection/universal property,
without presupposing that it gives a sigma-algebra. Sequences are indexed by ℕ;
the underlying type may be empty.
-/

open Set
open scoped MeasureTheory

universe u

namespace Specs.D11.Ch01.SetMonotoneClass

/-- The two closure properties in the source definition of a monotone class. -/
def IsMonotoneClass {α : Type u} (M : Set (Set α)) : Prop :=
  (∀ E : ℕ → Set α, Monotone E → (∀ n, E n ∈ M) → (⋃ n, E n) ∈ M) ∧
  (∀ E : ℕ → Set α, Antitone E → (∀ n, E n ∈ M) → (⋂ n, E n) ∈ M)

/-- Intersection of all monotone classes containing the given family. -/
def monotoneClosure {α : Type u} (A : Set (Set α)) : Set (Set α) :=
  {s | ∀ M : Set (Set α), IsMonotoneClass M → A ⊆ M → s ∈ M}

def IsMonotoneClass_type := ∀ {α : Type u}, Set (Set α) → Prop
def IsMonotoneClass_value : IsMonotoneClass_type.{u} := @IsMonotoneClass

def monotoneClosure_type := ∀ {α : Type u}, Set (Set α) → Set (Set α)
def monotoneClosure_value : monotoneClosure_type.{u} := @monotoneClosure

def closure_contains : Prop :=
  ∀ {α : Type u} (A : Set (Set α)), A ⊆ monotoneClosure A

def closure_minimal : Prop :=
  ∀ {α : Type u} {A M : Set (Set α)},
    IsMonotoneClass M → A ⊆ M → monotoneClosure A ⊆ M

def closure_isMonotoneClass : Prop :=
  ∀ {α : Type u} (A : Set (Set α)), IsMonotoneClass (monotoneClosure A)

def measurableSets_isMonotoneClass : Prop :=
  ∀ {α : Type u} (m : MeasurableSpace α),
    IsMonotoneClass {s : Set α | MeasurableSet[m] s}

/-- The full equality of the two generated families in the source theorem. -/
def monotoneClosure_eq_generated : Prop :=
  ∀ {α : Type u} {A : Set (Set α)}, MeasureTheory.IsSetAlgebra A →
    monotoneClosure A = {s : Set α | MeasurableSet[MeasurableSpace.generateFrom A] s}

/-- The usual application: a monotone class containing an algebra contains its
entire generated sigma-algebra, with no assumption that the class is an algebra. -/
def monotone_class : Prop :=
  ∀ {α : Type u} {A M : Set (Set α)},
    MeasureTheory.IsSetAlgebra A → IsMonotoneClass M → A ⊆ M →
    ∀ {s : Set α}, MeasurableSet[MeasurableSpace.generateFrom A] s → s ∈ M

end Specs.D11.Ch01.SetMonotoneClass
