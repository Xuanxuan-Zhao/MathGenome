import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ForwardPresentations
import Mathlib.Data.Quot

/-! W68: parallelism and representatives on nonloops. The subtype used for the
representative map includes membership in the ground. Thus neither ambient
points outside the ground nor loops acquire representatives. Singleton closure
classes are used to make a choice without presupposing the rank criterion. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u
variable {α : Type u}

def ParallelRelated (M : _root_.Matroid α) [M.Finite] (e f : α) : Prop :=
  e = f ∨ (e ≠ f ∧ rank M {e, f} = 1)

/-- Auxiliary quotient for choosing representatives, defined without a theorem
about rank. Its carrier consists only of nonloops. -/
def nonloopClosureSetoid (M : _root_.Matroid α) : Setoid {e // M.IsNonloop e} where
  r e f := M.closure {e.val} = M.closure {f.val}
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

noncomputable def parallelRepresentative (M : _root_.Matroid α)
    (e : {e // M.IsNonloop e}) : {e // M.IsNonloop e} :=
  (Quotient.mk (nonloopClosureSetoid M) e).out

noncomputable def parallelRepresentatives (M : _root_.Matroid α) : Set α :=
  Set.range (fun e : {e // M.IsNonloop e} => (parallelRepresentative M e).val)

/-- Exactly one nonloop in each nonloop parallel class. -/
def IsParallelRepresentativeSet (M : _root_.Matroid α) [M.Finite] (S : Set α) : Prop :=
  (∀ s ∈ S, M.IsNonloop s) ∧
    ∀ e, M.IsNonloop e → ∃! s, s ∈ S ∧ ParallelRelated M e s

/-- The image of the nonloops in A under the representative map. -/
noncomputable def parallelImage (M : _root_.Matroid α) (A : Set α) : Set α :=
  (fun e : {e // M.IsNonloop e} => (parallelRepresentative M e).val) ''
    {e | e.val ∈ A}

def ParallelRelatedType :=
  ∀ {α : Type u}, (M : _root_.Matroid α) → [M.Finite] → α → α → Prop

def nonloopClosureSetoidType :=
  ∀ {α : Type u}, (M : _root_.Matroid α) → Setoid {e // M.IsNonloop e}

def parallelRepresentativeType :=
  ∀ {α : Type u}, (M : _root_.Matroid α) →
    {e // M.IsNonloop e} → {e // M.IsNonloop e}

def parallelRepresentativesType :=
  ∀ {α : Type u}, _root_.Matroid α → Set α

def IsParallelRepresentativeSetType :=
  ∀ {α : Type u}, (M : _root_.Matroid α) → [M.Finite] → Set α → Prop

def parallelImageType :=
  ∀ {α : Type u}, _root_.Matroid α → Set α → Set α

def nonloopCharacterization : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) (e : α),
    M.IsNonloop e ↔ e ∈ M.E ∧ ¬ M.IsCircuit {e}

def parallelClosure : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] {e f : α},
    M.IsNonloop e → M.IsNonloop f →
      (ParallelRelated M e f ↔ M.closure {e} = M.closure {f})

def parallelRankCriterion : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] {e f : α},
    M.IsNonloop e → M.IsNonloop f → e ≠ f →
      (ParallelRelated M e f ↔ rank M {e, f} = 1)

def parallelEquivalence : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
    Equivalence (fun e f : {e // M.IsNonloop e} => ParallelRelated M e.val f.val)

def parallelRepresentative_related : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (e : {e // M.IsNonloop e}), ParallelRelated M e.val (parallelRepresentative M e).val

def parallelRepresentative_eq_iff : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (e f : {e // M.IsNonloop e}),
    parallelRepresentative M e = parallelRepresentative M f ↔ ParallelRelated M e.val f.val

def parallelRepresentatives_ground : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α), parallelRepresentatives M ⊆ M.E

def parallelRepresentatives_spec : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
    IsParallelRepresentativeSet M (parallelRepresentatives M)

def parallelRepresentative_mem : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) (e : {e // M.IsNonloop e}),
    (parallelRepresentative M e).val ∈ parallelRepresentatives M

def parallelRepresentative_fixed : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (s : {e // M.IsNonloop e}), s.val ∈ parallelRepresentatives M →
      parallelRepresentative M s = s

def parallelImage_mem : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) (A : Set α) (s : α),
    s ∈ parallelImage M A ↔
      ∃ e : {e // M.IsNonloop e}, e.val ∈ A ∧ (parallelRepresentative M e).val = s

def parallelImage_subset : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) (A : Set α),
    parallelImage M A ⊆ parallelRepresentatives M

def parallelRepresentatives_finite : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
    (parallelRepresentatives M).Finite

def parallelRepresentatives_empty : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α),
    (∀ e ∈ M.E, M.IsLoop e) → parallelRepresentatives M = ∅

def parallelImage_empty : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) (A : Set α),
    (∀ e ∈ A, ¬ M.IsNonloop e) → parallelImage M A = ∅

end FiniteCombinatorics.Matroid.Expected
