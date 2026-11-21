import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ParallelClasses

/-! W68, simplification. A representative map is defined only on nonloops;
its image on A therefore discards loops. All choices satisfying the upstream
representative-set predicate are allowed, on the original ambient type.
Simplicity means no ground loops and no distinct parallel ground elements. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set
open scoped _root_.Matroid
universe u
variable {α : Type u}

def representativeImage (M : _root_.Matroid α)
    (q : {e // M.IsNonloop e} → α) (A : Set α) : Set α :=
  q '' {e | e.val ∈ A}

def IsRepresentativeMap (M : _root_.Matroid α) [M.Finite] (S : Set α)
    (q : {e // M.IsNonloop e} → α) : Prop :=
  ∀ e, q e ∈ S ∧ ParallelRelated M e.val (q e)

def IsSimple (M : _root_.Matroid α) [M.Finite] : Prop :=
  (∀ e ∈ M.E, M.IsNonloop e) ∧
    ∀ e ∈ M.E, ∀ f ∈ M.E, ParallelRelated M e f → e = f

def representativeImageType := ∀ {α : Type u}, (M : _root_.Matroid α) →
  ({e // M.IsNonloop e} → α) → Set α → Set α

def IsRepresentativeMapType := ∀ {α : Type u}, (M : _root_.Matroid α) →
  [M.Finite] → Set α → ({e // M.IsNonloop e} → α) → Prop

def IsSimpleType := ∀ {α : Type u}, (M : _root_.Matroid α) → [M.Finite] → Prop

def representativeChoice : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
  ∃ (S : Set α) (q : {e // M.IsNonloop e} → α),
    IsParallelRepresentativeSet M S ∧ IsRepresentativeMap M S q

def representativeClosure : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α),
  IsParallelRepresentativeSet M S → IsRepresentativeMap M S q →
    ∀ A, A ⊆ M.E → M.closure (representativeImage M q A) = M.closure A

def simplificationSimple : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (hS : IsParallelRepresentativeSet M S),
  letI : (M ↾ S).Finite := M.restrict_finite
    (M.ground_finite.subset (fun s hs => (hS.1 s hs).mem_ground))
  IsSimple (M ↾ S)

def simplificationRank : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (hS : IsParallelRepresentativeSet M S)
    (q : {e // M.IsNonloop e} → α), IsRepresentativeMap M S q →
  ∀ A, A ⊆ M.E →
    letI : (M ↾ S).Finite := M.restrict_finite
      (M.ground_finite.subset (fun s hs => (hS.1 s hs).mem_ground))
    rank (M ↾ S) (representativeImage M q A) = rank M A

def simplificationClosure : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α),
  IsParallelRepresentativeSet M S → IsRepresentativeMap M S q →
    ∀ A, A ⊆ M.E →
      (M ↾ S).closure (representativeImage M q A) = M.closure A ∩ S

def simplificationAllLoops : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α),
  IsParallelRepresentativeSet M S → (∀ e ∈ M.E, M.IsLoop e) →
    S = ∅ ∧ ∀ A, representativeImage M q A = ∅

def simplificationRankZero : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α),
  IsParallelRepresentativeSet M S → rank M M.E = 0 →
    S = ∅ ∧ ∀ A, representativeImage M q A = ∅

def simplificationEmptyGround : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (S : Set α) (q : {e // M.IsNonloop e} → α),
  IsParallelRepresentativeSet M S → M.E = ∅ →
    S = ∅ ∧ ∀ A, representativeImage M q A = ∅

/-- The already chosen upstream map realizes the general construction with the
same image q(A) used upstream. -/
def canonicalRepresentativeMap : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
  IsRepresentativeMap M (parallelRepresentatives M)
    (fun e => (parallelRepresentative M e).val) ∧
  ∀ A, representativeImage M (fun e => (parallelRepresentative M e).val) A = parallelImage M A

end FiniteCombinatorics.Matroid.Expected
