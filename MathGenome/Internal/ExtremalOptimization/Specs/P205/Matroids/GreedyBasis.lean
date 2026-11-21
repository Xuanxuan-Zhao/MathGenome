import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Models
import Mathlib.Data.List.Basic

/-! Independent specification of paper.tex, Theorem 9.1 (W44).
An ordering is an arbitrary exhaustive list without repetitions, nonincreasing
in the given real weights. No sign restriction is imposed, including at the
last step. Prefix indices saturate at the length of the list. -/
namespace Specs.P205.Matroids
open _root_.P205.Matroids
noncomputable section
universe u

def greedyStepType := ∀ {α : Type u} (M : Matroid α), Set α → M.E → Set α

def greedyStepValue : greedyStepType.{u} := fun {α} M I e => by
  classical
  exact if M.Indep (insert (e : α) I) then insert (e : α) I else I

def greedyStateType := ∀ {α : Type u} (M : Matroid α), List M.E → ℕ → Set α

def greedyStateValue : greedyStateType.{u} := fun {_} M l i =>
  (l.take i).foldl (greedyStepValue M) ∅

def greedyOutputType := ∀ {α : Type u} (M : Matroid α), List M.E → Set α

def greedyOutputValue : greedyOutputType.{u} := fun {_} M l =>
  greedyStateValue M l l.length

def greedyPrefixType := ∀ {α : Type u} (M : Matroid α), List M.E → ℕ → Set α

def greedyPrefixValue : greedyPrefixType.{u} := fun {α} _M l i =>
  {x | ∃ e ∈ l.take i, (e : α) = x}

def GreedyOrderingType := ∀ {α : Type u} (M : Matroid α), Coordinates M → List M.E → Prop

def GreedyOrderingValue : GreedyOrderingType.{u} := fun {_} _ w l =>
  l.Nodup ∧ (∀ e, e ∈ l) ∧ l.Pairwise (fun a b => w b ≤ w a)

/-- Every prefix of the actual scan is a basis of that prefix. -/
def GreedyPrefixBasis : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (w : Coordinates M)
    (l : List M.E), GreedyOrderingValue M w l → ∀ i : ℕ,
    M.IsBasis (greedyStateValue M l i) (greedyPrefixValue M l i)

/-- Later steps never select a previously rejected prefix element. -/
def GreedyOutputInterPrefix : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (w : Coordinates M)
    (l : List M.E), GreedyOrderingValue M w l → ∀ i : ℕ,
    greedyOutputValue M l ∩ greedyPrefixValue M l i = greedyStateValue M l i

/-- The final output attains all prefix rank bounds simultaneously. -/
def GreedyPrefixRank : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (w : Coordinates M)
    (l : List M.E), GreedyOrderingValue M w l → ∀ i : ℕ,
    (greedyOutputValue M l ∩ greedyPrefixValue M l i).ncard =
      rankValue M (greedyPrefixValue M l i)

/-- All exhaustive nonincreasing orders, with arbitrary ties, give an optimal basis.
In particular this includes the empty list on empty ground and negative weights. -/
def GreedyBasisOptimal : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (w : Coordinates M)
    (l : List M.E), GreedyOrderingValue M w l →
    M.IsBase (greedyOutputValue M l) ∧
      ∀ B : Set α, M.IsBase B →
        subsetSumValue M w B ≤ subsetSumValue M w (greedyOutputValue M l)

end
end Specs.P205.Matroids
