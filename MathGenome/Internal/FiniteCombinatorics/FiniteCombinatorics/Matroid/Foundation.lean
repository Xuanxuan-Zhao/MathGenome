import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation

/-! The canonical matroid is Mathlib's `Matroid α`, with `[M.Finite]`
meaning that `M.E` is finite, rather than requiring a finite ambient type.
We use its predicates `M.IsBasis I A`, `M.IsBase B`, `M.IsCircuit C`,
and its function `M.closure A` throughout. The construction below keeps
the ambient type, ground and independence predicate exactly as supplied.

Presentation functions are defined on ambient sets but constrained only
on subsets of the designated ground; their values elsewhere are irrelevant.
The independent Expected values in the Specs provide these same interfaces
to downstream Specs without importing this implementation. -/

namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u}

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

instance {E : Set α} (S : IndependenceSystem E) (h : Augmentation S) :
    (ofAugmentation S h).Finite := ⟨S.finite_ground⟩

theorem groundPreserved :
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S),
    (ofAugmentation S h).E = E := by
  intro E S h
  rfl

theorem indepPreserved :
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S) (I : Set α),
    (ofAugmentation S h).Indep I ↔ S.Indep I := by
  intro E S h I
  rfl

theorem basisPreserved :
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S)
    (A I : Set α), A ⊆ E →
      ((ofAugmentation S h).IsBasis I A ↔ BasisIn S A I) := by
  intro E S h A I hA
  rw [_root_.Matroid.isBasis_iff (by exact hA)]
  change (S.Indep I ∧ I ⊆ A ∧
    ∀ J, S.Indep J → I ⊆ J → J ⊆ A → I = J) ↔
    (I ⊆ A ∧ S.Indep I ∧ ∀ J, J ⊆ A → S.Indep J → I ⊆ J → J = I)
  constructor
  · rintro ⟨hi, hIA, hmax⟩
    exact ⟨hIA, hi, fun J hJA hJ hIJ => (hmax J hJ hIJ hJA).symm⟩
  · rintro ⟨hIA, hi, hmax⟩
    exact ⟨hi, hIA, fun J hJ hIJ hJA => (hmax J hJA hJ hIJ).symm⟩

theorem basePreserved :
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S) (I : Set α),
    (ofAugmentation S h).IsBase I ↔ MaximalIndependent S I := by
  intro E S h I
  rw [← _root_.Matroid.isBasis_ground_iff]
  exact basisPreserved E S h E I Subset.rfl

theorem finiteConstruction :
  ∀ (E : Set α) (S : IndependenceSystem E) (h : Augmentation S),
    (ofAugmentation S h).Finite := by
  intro E S h
  exact ⟨S.finite_ground⟩

theorem finiteRankBridge :
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    ((M.eRk A).toNat : ℕ∞) = M.eRk A := by
  intro M hM A
  exact ENat.natCast_toNat (M.isRkFinite_set A).eRk_lt_top.ne

theorem integerRankBridge :
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    rank M A = ((M.eRk A).toNat : ℤ) := by
  intro M hM A
  rfl

theorem emptyIndependence :
  ∀ (S : IndependenceSystem (∅ : Set α)) (I : Set α), S.Indep I ↔ I = ∅ := by
  intro S I
  constructor
  · intro hi
    exact Set.subset_empty_iff.mp (S.subset_ground hi)
  · rintro rfl
    exact S.empty_indep

theorem emptyBasis :
  ∀ (S : IndependenceSystem (∅ : Set α)) (I : Set α),
    MaximalIndependent S I ↔ I = ∅ := by
  intro S I
  constructor
  · intro hi
    exact Set.subset_empty_iff.mp hi.1
  · rintro rfl
    exact ⟨Subset.rfl, S.empty_indep, fun J hJ _ _ => Set.subset_empty_iff.mp hJ⟩

end FiniteCombinatorics.Matroid
