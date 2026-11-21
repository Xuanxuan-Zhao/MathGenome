import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.ZeroCovers
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.Perfect
import Mathlib.Data.Fintype.Pi

/-! Independent statements for K03.08.cantor_set (paper.tex:2177–2206).
Finite binary words label the surviving closed intervals; their cardinality is 2^n.
The stages and limit are the standard middle-thirds construction. -/
namespace Specs.SingleVariableAnalysis.Ch08.CantorSet

open Set
open scoped BigOperators

/-- Left endpoint of the component addressed by a binary word, most significant digit first. -/
noncomputable def left : (n : ℕ) → (Fin n → Bool) → ℝ
  | 0, _ => 0
  | n + 1, w => ((if w 0 then 2 else 0) + left n (fun i => w i.succ)) / 3

noncomputable def right (n : ℕ) (w : Fin n → Bool) : ℝ := left n w + (1 / 3 : ℝ)^n

def stageType := ℕ → Set ℝ
noncomputable def stageValue : ℕ → Set ℝ := preCantorSet

def setType := Set ℝ
noncomputable def setValue : Set ℝ := ⋂ n, stageValue n

def leftType := (n : ℕ) → (Fin n → Bool) → ℝ
noncomputable def leftValue : leftType := left
noncomputable def rightValue : leftType := right

def initialStage : Prop := stageValue 0 = Icc 0 1

def intersection : Prop := setValue = ⋂ n, stageValue n

def stageComponents : Prop := ∀ n : ℕ,
  Fintype.card (Fin n → Bool) = 2^n ∧
  stageValue n = ⋃ w : Fin n → Bool, Icc (left n w) (right n w) ∧
  (∀ w, right n w - left n w = (1 / 3 : ℝ)^n) ∧
  (∀ w, left n w < right n w) ∧
  Pairwise (fun v w : Fin n → Bool =>
    Disjoint (Icc (left n v) (right n v)) (Icc (left n w) (right n w)))

/-- Exactly the middle open third is removed from each surviving component. -/
def deleteMiddleThirds : Prop := ∀ n : ℕ,
  stageValue (n+1) = ⋃ w : Fin n → Bool,
    (Icc (left n w) (right n w) \
      Ioo (left n w + (right n w - left n w)/3)
        (right n w - (right n w - left n w)/3))

def stageTotalLength : Prop := ∀ n : ℕ,
  (∑ w : Fin n → Bool, (right n w - left n w)) = (2/3 : ℝ)^n

def nested : Prop := Antitone stageValue

def endpointsRemain : Prop := ∀ (n : ℕ) (w : Fin n → Bool),
  left n w ∈ setValue ∧ right n w ∈ setValue

def nonemptyCompact : Prop := setValue.Nonempty ∧ IsCompact setValue ∧
  (0 : ℝ) ∈ setValue ∧ (1 : ℝ) ∈ setValue

def perfectSet : Prop := Perfect setValue

def emptyInterior : Prop := interior setValue = ∅

def lengthZero : Prop := ZeroCovers.lengthZeroValue setValue

def ternaryMembership : Prop := ∀ x : ℝ, x ∈ setValue ↔
  ∃ a : ℕ → Fin 3, (∀ i, a i = 0 ∨ a i = 2) ∧ Real.ofDigits a = x

def endpointExpansion : Prop :=
  Real.ofDigits (fun n => if n = 0 then (0 : Fin 3) else 2) = (1 / 3 : ℝ) ∧
  (1 / 3 : ℝ) ∈ setValue

end Specs.SingleVariableAnalysis.Ch08.CantorSet
