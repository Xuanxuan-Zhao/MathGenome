import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.FiniteModels
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Ramsey.GraphNumbers
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory
open scoped BigOperators Classical

namespace P205.Probability.RandomRamsey
open P205.Ramsey

/-- One fair red-blue bit, including both colors with weight one half. -/
noncomputable def fairBit : FiniteModel (Fin 2) where
  weight _ := 1 / 2
  weight_nonneg _ := by norm_num
  weight_sum := by simp

abbrev Edge (n : ℕ) := KSubsets (Fin n) 2
noncomputable instance edgeDecidableEq (n : ℕ) : DecidableEq (Edge n) := Classical.decEq _

abbrev Coloring (n : ℕ) := Edge n → Fin 2

/-- Independent fair colors on the unordered edges of the complete graph. -/
noncomputable def experiment (n : ℕ) : FiniteModel (Coloring n) :=
  FiniteModel.pi (fun _ : Edge n => fairBit)

/-- All internal edges of a vertex set have the specified color. -/
def pattern {n : ℕ} (t : Finset (Fin n)) (d : Fin 2) : Set (Coloring n) :=
  {c | ColoredClique c d t}

def monochromatic {n : ℕ} (t : Finset (Fin n)) : Set (Coloring n) :=
  {c | ∃ d, ColoredClique c d t}

namespace Specs

def IndependentEdges : Prop :=
  letI : MeasurableSpace (Fin 2) := ⊤
  ∀ n : ℕ,
  ProbabilityTheory.iIndepFun (fun e (c : Coloring n) => c e)
    (experiment n).measure

def FairEdge : Prop := ∀ (n : ℕ) (e : Edge n) (d : Fin 2),
  (experiment n).eventMass {c | c e = d} = 1 / 2

def PatternProbability : Prop := ∀ (n k : ℕ) (t : Finset (Fin n)),
  t.card = k → ∀ d : Fin 2,
  (experiment n).eventMass (pattern t d) = (1 / 2 : ℝ) ^ (Nat.choose k 2)

def MonochromaticProbability : Prop := ∀ (n k : ℕ), 2 ≤ k →
  ∀ t : Finset (Fin n), t.card = k →
  (experiment n).eventMass (monochromatic t) =
    (2 : ℝ) ^ ((1 : ℤ) - (Nat.choose k 2 : ℤ))

def LowerBound : Prop := ∀ (n k : ℕ), 2 ≤ k →
  (Nat.choose n k : ℝ) * (2 : ℝ) ^ ((1 : ℤ) - (Nat.choose k 2 : ℤ)) < 1 →
  n < P205.Ramsey.Specs.ramseyNumberValue k k

def ExponentialLowerBound : Prop := ∀ k : ℕ, 3 ≤ k →
  (2 : ℝ) ^ ((k : ℝ) / 2) < (P205.Ramsey.Specs.ramseyNumberValue k k : ℝ)

end Specs
end P205.Probability.RandomRamsey
