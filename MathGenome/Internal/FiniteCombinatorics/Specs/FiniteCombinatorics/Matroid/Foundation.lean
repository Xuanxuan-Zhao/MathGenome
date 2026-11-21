import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Closure

/-! Finite matroid conventions for paper.tex, Chapter 10, W64.
The ambient type need not be finite. Every ground is a finite set in it;
independence is false off the powerset of that ground. Functions representing
rank and closure are constrained only on that powerset. Complements are relative.
The empty circuit family is permitted. -/

namespace FiniteCombinatorics.Matroid

open Set
universe u
variable {α : Type u}

/-- A hereditary family on a specified finite ground, including the empty set. -/
structure IndependenceSystem (E : Set α) where
  finite_ground : E.Finite
  Indep : Set α → Prop
  empty_indep : Indep ∅
  hereditary : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I
  subset_ground : ∀ ⦃I⦄, Indep I → I ⊆ E

namespace Expected

def Augmentation {E : Set α} (S : IndependenceSystem E) : Prop :=
  ∀ ⦃I J⦄, S.Indep I → S.Indep J → I.ncard < J.ncard →
    ∃ e ∈ J \ I, S.Indep (insert e I)

/-- Maximal by inclusion, not merely of maximum cardinality. -/
def BasisIn {E : Set α} (S : IndependenceSystem E) (A I : Set α) : Prop :=
  I ⊆ A ∧ S.Indep I ∧
    ∀ J, J ⊆ A → S.Indep J → I ⊆ J → J = I

def MaximalIndependent {E : Set α} (S : IndependenceSystem E) (I : Set α) : Prop :=
  BasisIn S E I

def BasisPresentation (E : Set α) (B : Set (Set α)) : Prop :=
  B.Nonempty ∧ (∀ D ∈ B, D ⊆ E) ∧
    ∀ D ∈ B, ∀ F ∈ B, ∀ e ∈ D \ F,
      ∃ f ∈ F \ D, insert f (D \ {e}) ∈ B

/-- Subtraction here is subtraction in ℤ, including for arbitrary input data. -/
def RankPresentation (E : Set α) (r : Set α → ℤ) : Prop :=
  r ∅ = 0 ∧
    (∀ A, A ⊆ E → ∀ e ∈ E, 0 ≤ r (insert e A) - r A ∧
      r (insert e A) - r A ≤ 1) ∧
    ∀ A, A ⊆ E → ∀ B, B ⊆ E →
      r (A ∪ B) + r (A ∩ B) ≤ r A + r B

def CircuitPresentation (E : Set α) (C : Set (Set α)) : Prop :=
  (∀ D ∈ C, D ⊆ E ∧ D.Nonempty) ∧
    (∀ D ∈ C, ∀ F ∈ C, D ⊆ F → D = F) ∧
    ∀ D ∈ C, ∀ F ∈ C, D ≠ F → ∀ e ∈ D ∩ F,
      ∃ K ∈ C, K ⊆ (D ∪ F) \ {e}

/-- The range condition makes this a map from 2^E to 2^E. -/
def ClosurePresentation (E : Set α) (cl : Set α → Set α) : Prop :=
  (∀ A, A ⊆ E → cl A ⊆ E) ∧
    (∀ A, A ⊆ E → A ⊆ cl A) ∧
    (∀ A, A ⊆ E → ∀ B, B ⊆ E → A ⊆ B → cl A ⊆ cl B) ∧
    (∀ A, A ⊆ E → cl (cl A) = cl A) ∧
    ∀ A, A ⊆ E → ∀ x ∈ E, ∀ y ∈ E,
      y ∈ cl (insert x A) \ cl A → x ∈ cl (insert y A)

def BasisIndependent (E : Set α) (B : Set (Set α)) (I : Set α) : Prop :=
  I ⊆ E ∧ ∃ D ∈ B, I ⊆ D

def RankIndependent (E : Set α) (r : Set α → ℤ) (I : Set α) : Prop :=
  I ⊆ E ∧ r I = (I.ncard : ℤ)

def CircuitIndependent (E : Set α) (C : Set (Set α)) (I : Set α) : Prop :=
  I ⊆ E ∧ ∀ D ∈ C, ¬ D ⊆ I

def ClosureIndependent (E : Set α) (cl : Set α → Set α) (I : Set α) : Prop :=
  I ⊆ E ∧ ∀ e ∈ I, e ∉ cl (I \ {e})

def relativeCompl (E A : Set α) : Set α := E \ A

/-- Finite natural extended rank cast into ℤ. No truncated subtraction is used. -/
noncomputable def rank (M : _root_.Matroid α) [M.Finite] (A : Set α) : ℤ :=
  ((M.eRk A).toNat : ℤ)

/-- Use the same Mathlib matroid and ambient type for every minor. -/
def fromMatroid (M : _root_.Matroid α) [M.Finite] : IndependenceSystem M.E where
  finite_ground := M.ground_finite
  Indep := M.Indep
  empty_indep := M.empty_indep
  hereditary := fun {_ _} h hIJ => h.subset hIJ
  subset_ground := fun {_} h => h.subset_ground

/-- The canonical construction from finite augmentation. -/
def ofAugmentation {E : Set α} (S : IndependenceSystem E) (h : Augmentation S) :
    _root_.Matroid α :=
  (IndepMatroid.ofFinite S.finite_ground S.Indep S.empty_indep
    S.hereditary (fun {_ _} hI hJ hcard =>
      let ⟨e, he, hi⟩ := h hI hJ hcard
      ⟨e, he.1, he.2, hi⟩) S.subset_ground).matroid

def AugmentationType := ∀ {α : Type u}, {E : Set α} → IndependenceSystem E → Prop

def BasisInType := ∀ {α : Type u}, {E : Set α} → IndependenceSystem E → Set α → Set α → Prop

def MaximalIndependentType := ∀ {α : Type u}, {E : Set α} → IndependenceSystem E → Set α → Prop

def BasisPresentationType := ∀ {α : Type u}, Set α → Set (Set α) → Prop

def RankPresentationType := ∀ {α : Type u}, Set α → (Set α → ℤ) → Prop

def CircuitPresentationType := ∀ {α : Type u}, Set α → Set (Set α) → Prop

def ClosurePresentationType := ∀ {α : Type u}, Set α → (Set α → Set α) → Prop

def BasisIndependentType := ∀ {α : Type u}, Set α → Set (Set α) → Set α → Prop

def RankIndependentType := ∀ {α : Type u}, Set α → (Set α → ℤ) → Set α → Prop

def CircuitIndependentType := ∀ {α : Type u}, Set α → Set (Set α) → Set α → Prop

def ClosureIndependentType := ∀ {α : Type u}, Set α → (Set α → Set α) → Set α → Prop

def relativeComplType := ∀ {α : Type u}, Set α → Set α → Set α

def rankType := ∀ {α : Type u}, (M : _root_.Matroid α) → [M.Finite] → Set α → ℤ

def fromMatroidType := ∀ {α : Type u}, (M : _root_.Matroid α) → [M.Finite] → IndependenceSystem M.E

def ofAugmentationType := ∀ {α : Type u}, {E : Set α} → (S : IndependenceSystem E) → Augmentation S → _root_.Matroid α

def groundPreserved : Prop :=
  ∀ {α : Type u},
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S),
    (ofAugmentation S h).E = E

def indepPreserved : Prop :=
  ∀ {α : Type u},
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S) (I : Set α),
    (ofAugmentation S h).Indep I ↔ S.Indep I

def basisPreserved : Prop :=
  ∀ {α : Type u},
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S)
    (A I : Set α), A ⊆ E →
      ((ofAugmentation S h).IsBasis I A ↔ BasisIn S A I)

def basePreserved : Prop :=
  ∀ {α : Type u},
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S) (I : Set α),
    (ofAugmentation S h).IsBase I ↔ MaximalIndependent S I

def finiteConstruction : Prop :=
  ∀ {α : Type u},
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S),
    (ofAugmentation S h).Finite

def finiteRankBridge : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    ((M.eRk A).toNat : ℕ∞) = M.eRk A

def integerRankBridge : Prop :=
  ∀ {α : Type u},
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    rank M A = ((M.eRk A).toNat : ℤ)

def emptyIndependence : Prop :=
  ∀ {α : Type u},
  ∀ (S : IndependenceSystem (∅ : Set α)) (I : Set α), S.Indep I ↔ I = ∅

def emptyBasis : Prop :=
  ∀ {α : Type u},
  ∀ (S : IndependenceSystem (∅ : Set α)) (I : Set α),
    MaximalIndependent S I ↔ I = ∅

end Expected
end FiniteCombinatorics.Matroid
