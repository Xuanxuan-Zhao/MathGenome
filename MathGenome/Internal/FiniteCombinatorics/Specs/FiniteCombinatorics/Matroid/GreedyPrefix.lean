import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GreedyDefinition

/-! Independent statements for the prefix invariant, paper.tex:3313–3331.
The statements hold for every natural prefix index: taking a prefix saturates
at the length of the enumeration. In particular they include 0 ≤ i ≤ |E|.
Only the rank statements require augmentation. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u

def greedyPrefix_basisIn : Prop :=
  ∀ {α : Type u} {E : Set α} (S : IndependenceSystem E)
    (w : E → ℝ) (tie : LinearOrder E) (i : ℕ),
    BasisIn S (greedyPrefix S w tie i) (greedyState S w tie i)

def greedyOutput_inter_prefix : Prop :=
  ∀ {α : Type u} {E : Set α} (S : IndependenceSystem E)
    (w : E → ℝ) (tie : LinearOrder E) (i : ℕ),
    greedyOutput S w tie ∩ greedyPrefix S w tie i = greedyState S w tie i

def greedyOutput_maximal : Prop :=
  ∀ {α : Type u} {E : Set α} (S : IndependenceSystem E)
    (w : E → ℝ) (tie : LinearOrder E),
    MaximalIndependent S (greedyOutput S w tie)

def greedyPrefix_isBasis : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E) (i : ℕ),
    M.IsBasis (greedyState (fromMatroid M) w tie i)
      (greedyPrefix (fromMatroid M) w tie i)

def greedyPrefix_cardinality : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E) (i : ℕ),
    (greedyOutput (fromMatroid M) w tie ∩
      greedyPrefix (fromMatroid M) w tie i).ncard =
      (greedyState (fromMatroid M) w tie i).ncard ∧
    ((greedyState (fromMatroid M) w tie i).ncard : ℤ) =
      rank M (greedyPrefix (fromMatroid M) w tie i)

def greedyOutput_isBase : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E),
    M.IsBase (greedyOutput (fromMatroid M) w tie)

/-- The same rank conclusion directly for the original family with augmentation,
using its canonical matroid, with no replacement of its greedy run. -/
def greedyPrefix_augmented_cardinality : Prop :=
  ∀ {α : Type u} {E : Set α} (S : IndependenceSystem E) (h : Augmentation S)
    (w : E → ℝ) (tie : LinearOrder E) (i : ℕ),
    (greedyOutput S w tie ∩ greedyPrefix S w tie i).ncard =
      (greedyState S w tie i).ncard ∧
    letI : (ofAugmentation S h).Finite := ⟨S.finite_ground⟩
    ((greedyState S w tie i).ncard : ℤ) =
      rank (ofAugmentation S h) (greedyPrefix S w tie i)

def greedyOutput_augmented_isBase : Prop :=
  ∀ {α : Type u} {E : Set α} (S : IndependenceSystem E) (h : Augmentation S)
    (w : E → ℝ) (tie : LinearOrder E),
    (ofAugmentation S h).IsBase (greedyOutput S w tie)

end FiniteCombinatorics.Matroid.Expected
