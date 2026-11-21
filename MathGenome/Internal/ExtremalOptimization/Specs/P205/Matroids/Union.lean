import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.MaximumAssignableSize

/-! Matroid union, its actual rank, and the full disjoint partition criterion
(paper.tex, Theorem 9.9). No augmentation or submodularity certificate is assumed. -/
namespace Specs.P205.Matroids
open _root_.P205.Matroids Set
open scoped BigOperators
universe u

/-- Submodularity of the maximum computed before constructing the matroid. -/
def QSubmodular : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k) (S T : Set α),
    S ⊆ F.ground → T ⊆ F.ground →
    qValue F (S ∪ T) + qValue F (S ∩ T) ≤ qValue F S + qValue F T

/-- Structural augmentation for the original assignable sets. -/
def AssignableAugmentation : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k) (I J : Set α),
    AssignableValue F I → AssignableValue F J → I.ncard < J.ncard →
    ∃ e ∈ J, e ∉ I ∧ AssignableValue F (insert e I)

/-- Construct a genuine finite matroid on exactly E, identify independence,
identify its canonical rank with q, and give its attained minimum formula. -/
def UnionExistence : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k),
    ∃ M : Matroid α, M.E = F.ground ∧ M.Finite ∧
      (∀ I : Set α, M.Indep I ↔ AssignableValue F I) ∧
      (∀ S : Set α, S ⊆ F.ground → rankValue M S = qValue F S) ∧
      (∀ S : Set α, S ⊆ F.ground →
        (∃ T : Set α, T ⊆ S ∧
          rankValue M S = (S \ T).ncard + ∑ i, rankValue (F.matroid i) T) ∧
        (∀ T : Set α, T ⊆ S →
          rankValue M S ≤ (S \ T).ncard + ∑ i, rankValue (F.matroid i) T))

/-- Parts are pairwise disjoint, have union exactly S, and may be empty. -/
def PartitionCriterion : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k) (S : Set α), S ⊆ F.ground →
    ((∃ parts : Fin k → Set α, DisjointAssignment F S S parts) ↔
      ∀ T : Set α, T ⊆ S → T.ncard ≤ ∑ i, rankValue (F.matroid i) T)

/-- The empty family still has ground E; its only independent set is empty. -/
def UnionZero : Prop :=
  ∀ {α : Type u} (F : Family α 0),
    ∃ M : Matroid α, M.E = F.ground ∧ M.Finite ∧
      (∀ I : Set α, M.Indep I ↔ I = ∅) ∧
      (∀ S : Set α, S ⊆ F.ground → rankValue M S = 0)

/-- For k=0 the partition criterion holds precisely for the empty subset. -/
def PartitionZero : Prop :=
  ∀ {α : Type u} (F : Family α 0) (S : Set α), S ⊆ F.ground →
    ((∃ parts : Fin 0 → Set α, DisjointAssignment F S S parts) ↔ S = ∅) ∧
    ((∀ T : Set α, T ⊆ S → T.ncard ≤ ∑ i, rankValue (F.matroid i) T) ↔ S = ∅)

end Specs.P205.Matroids
