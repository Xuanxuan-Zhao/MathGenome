import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.FiniteModels
import Mathlib.Order.Partition.Finpartition

/-! Finite staged revelation, paper.tex 873–904 (general part of W19).
A partition is an actual partition of all outcomes into nonempty disjoint cells.
`Q ≤ P` means that Q refines P. A stage sequence is indexed by natural numbers,
with only indices 0 through n relevant; thus n = 0 is permitted.
Conditional means have a positive-mass cell as their domain. -/

open scoped BigOperators Classical

namespace P205.Probability.ConditionalSelection

abbrev Partition (Ω : Type*) [Fintype Ω] := Finpartition (Finset.univ : Finset Ω)

variable {Ω : Type*} [Fintype Ω]

noncomputable def cellMass (M : FiniteModel Ω) (C : Finset Ω) : ℝ :=
  M.eventMass (C : Set Ω)

noncomputable def cellMoment (M : FiniteModel Ω) (Z : Ω → ℝ) (C : Finset Ω) : ℝ :=
  ∑ ω ∈ C, M.weight ω * Z ω

abbrev PositiveCell (M : FiniteModel Ω) := {C : Finset Ω // 0 < cellMass M C}

noncomputable def mean (M : FiniteModel Ω) (Z : Ω → ℝ) (C : PositiveCell M) : ℝ :=
  cellMoment M Z C.val / cellMass M C.val

noncomputable def children (Q : Partition Ω) (C : Finset Ω) : Finset (Finset Ω) :=
  Q.parts.filter (fun D => D ⊆ C)

noncomputable def positiveChildren (M : FiniteModel Ω) (Q : Partition Ω)
    (C : Finset Ω) : Finset (PositiveCell M) :=
  (children Q C).subtype (fun D => 0 < cellMass M D)

/-- A path records membership and the local nondecreasing selection rule.
Positivity at every stage is part of the type of C. -/
def StagePath (M : FiniteModel Ω) (Z : Ω → ℝ) (P : ℕ → Partition Ω)
    (n : ℕ) (C : ℕ → PositiveCell M) : Prop :=
  (C 0).val = Finset.univ ∧
  (∀ i, i ≤ n → (C i).val ∈ (P i).parts) ∧
  (∀ i, i < n → (C (i + 1)).val ⊆ (C i).val ∧ mean M Z (C i) ≤ mean M Z (C (i + 1)))

end ConditionalSelection

namespace ConditionalSelectionSpec
open ConditionalSelection

noncomputable def conditionalMeanType := ∀ {Ω : Type*} [Fintype Ω]
  (M : FiniteModel Ω), (Ω → ℝ) → PositiveCell M → ℝ

noncomputable def conditionalMeanValue : conditionalMeanType := mean

def positiveChildMasses : Prop := ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω)
  (P Q : Partition Ω) (_hQP : Q ≤ P) (C : PositiveCell M), C.val ∈ P.parts →
  (∑ D ∈ positiveChildren M Q C.val, cellMass M D.val) = cellMass M C.val

def parentMean : Prop := ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω) (Z : Ω → ℝ)
  (P Q : Partition Ω) (_hQP : Q ≤ P) (C : PositiveCell M), C.val ∈ P.parts →
  mean M Z C = ∑ D ∈ positiveChildren M Q C.val,
    (cellMass M D.val / cellMass M C.val) * mean M Z D

def localSelection : Prop := ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω) (Z : Ω → ℝ)
  (P Q : Partition Ω) (_hQP : Q ≤ P) (C : PositiveCell M), C.val ∈ P.parts →
  ∃ D ∈ positiveChildren M Q C.val, mean M Z C ≤ mean M Z D

def stagedRealization : Prop := ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω)
  (Z : Ω → ℝ) (n : ℕ) (P : ℕ → Partition Ω),
  (P 0).parts = {Finset.univ} →
  (P n).parts = Finset.univ.image (fun ω : Ω => ({ω} : Finset Ω)) →
  (∀ i, i < n → P (i + 1) ≤ P i) →
  ∃ C : ℕ → PositiveCell M, StagePath M Z P n C ∧
    ∃ ω : Ω, (C n).val = {ω} ∧ 0 < M.weight ω ∧ mean M Z (C n) = Z ω ∧
      M.expectation Z ≤ Z ω

end ConditionalSelectionSpec
end P205.Probability
