import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.RandomGraphCycles
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open scoped BigOperators Classical

namespace P205.Probability.RandomGraphIndependence
open RandomGraphCycles

/-- The integer threshold used in the alteration argument. -/
noncomputable def threshold (k n : ℕ) : ℕ := ⌈(n : ℝ) / (4 * (k : ℝ))⌉₊

/-- The exponential upper bound on the probability of a large independent set. -/
noncomputable def upperBound (g k n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * Real.exp (-parameter g n * ((threshold k n).choose 2 : ℝ))

end P205.Probability.RandomGraphIndependence

namespace Specs.P205.Probability.RandomGraphIndependence
open _root_.P205.Probability.RandomGraphCycles
open _root_.P205.Probability.RandomGraphIndependence

def IndependentSetProbability : Prop := ∀ (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n)
    (S : Finset (Fin n)),
  (model g n hg hn).eventMass {ω | (graph ω).IsIndepSet (S : Set (Fin n))} =
    (1 - parameter g n) ^ S.card.choose 2

def IndependenceBound : Prop := ∀ (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n) (a : ℕ),
  (model g n hg hn).eventMass {ω | a ≤ (graph ω).indepNum} ≤
    (n.choose a : ℝ) * (1 - parameter g n) ^ a.choose 2

def ExponentialBound : Prop := ∀ (g n : ℕ) (_hg : 3 ≤ g) (_hn : 1 ≤ n) (a : ℕ),
  (n.choose a : ℝ) * (1 - parameter g n) ^ a.choose 2 ≤
    (2 : ℝ) ^ n * Real.exp (-parameter g n * (a.choose 2 : ℝ))

def QuantitativeExponent : Prop := ∀ (g k n : ℕ), 3 ≤ g → 1 ≤ k → 8 * k ≤ n →
  (n : ℝ) ^ (1 + 1 / (2 * (g : ℝ))) / (64 * (k : ℝ) ^ 2) ≤
    parameter g n * ((threshold k n).choose 2 : ℝ)

def UpperBoundTendsToZero : Prop := ∀ (g k : ℕ), 3 ≤ g → 1 ≤ k →
  Filter.Tendsto (upperBound g k) Filter.atTop (nhds 0)

/-- A common outcome in the very same experiment satisfies both strict bounds. -/
def SimultaneousExistence : Prop := ∀ (g k : ℕ), 3 ≤ g → 1 ≤ k →
  ∃ (n : ℕ) (_hn : 1 ≤ n) (ω : Outcome n),
    count g n ω < (n : ℝ) / 2 ∧ (graph ω).indepNum < threshold k n

/-- The decoded finite graph, with the short cycles counted by their distinct edge sets. -/
def GoodGraphExists : Prop := ∀ (g k : ℕ), 3 ≤ g → 1 ≤ k →
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), 1 ≤ n ∧
    (∑ l ∈ Finset.Icc 3 g,
      (((cycles n l).filter (fun S => ∀ e ∈ S, e.val ∈ G.edgeSet)).card : ℝ)) < (n : ℝ) / 2 ∧
    G.indepNum < threshold k n

end Specs.P205.Probability.RandomGraphIndependence
