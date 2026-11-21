import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GreedyIndependent

/-! W80: both objectives, for an arbitrary fixed total tie order and for all
orders. `IndependenceSystem` includes the empty independent set, equivalently
nonemptiness of a hereditary family. No nonempty-ground hypothesis is imposed. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u

def nonnegative_maximal_extension : Prop :=
  ∀ {α : Type u} {E : Set α} (S : IndependenceSystem E) (w : E → ℝ),
    (∀ e, 0 ≤ w e) → ∀ I, S.Indep I →
    ∃ B, MaximalIndependent S B ∧ I ⊆ B ∧ subsetWeight S w I ≤ subsetWeight S w B

def greedy_objectives_iff : Prop :=
  ∀ {α : Type u} {E : Set α} (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E), (∀ e, 0 ≤ w e) →
    (BasisOptimal S w (greedyOutput S w tie) ↔
      IndependentOptimal S w (greedyOutput S w tie))

def greedy_characterization_fixed : Prop :=
  ∀ {α : Type u} {E : Set α} (S : IndependenceSystem E) (tie : LinearOrder E),
    (Augmentation S ↔ ∀ w : E → ℝ, (∀ e, 0 ≤ w e) →
      BasisOptimal S w (greedyOutput S w tie)) ∧
    (Augmentation S ↔ ∀ w : E → ℝ, (∀ e, 0 ≤ w e) →
      IndependentOptimal S w (greedyOutput S w tie))

def greedy_characterization_all : Prop :=
  ∀ {α : Type u} {E : Set α} (S : IndependenceSystem E),
    (Augmentation S ↔ ∀ (w : E → ℝ) (tie : LinearOrder E), (∀ e, 0 ≤ w e) →
      BasisOptimal S w (greedyOutput S w tie)) ∧
    (Augmentation S ↔ ∀ (w : E → ℝ) (tie : LinearOrder E), (∀ e, 0 ≤ w e) →
      IndependentOptimal S w (greedyOutput S w tie))

end FiniteCombinatorics.Matroid.Expected
