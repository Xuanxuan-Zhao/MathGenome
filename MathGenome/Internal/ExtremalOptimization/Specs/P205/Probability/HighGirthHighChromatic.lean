import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.RandomGraphIndependence
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

open scoped BigOperators Classical

namespace P205.Probability.HighGirthHighChromatic
open RandomGraphCycles RandomGraphIndependence

/-- Number of distinct short cycle edge sets in the original graph. -/
noncomputable def shortCycleCount {n : ℕ} (g : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  ∑ l ∈ Finset.Icc 3 g,
    ((cycles n l).filter (fun S => ∀ e ∈ S, e.val ∈ G.edgeSet)).card

/-- Direct cycle-length formulation, including acyclic graphs. -/
def NoShortCycles {V : Type*} (g : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (w : G.Walk v v), w.IsCycle → g < w.length

end P205.Probability.HighGirthHighChromatic

namespace Specs.P205.Probability.HighGirthHighChromatic
open _root_.P205.Probability.HighGirthHighChromatic
open _root_.P205.Probability.RandomGraphIndependence

/-- Removing at most one vertex per original short cycle eliminates them all. -/
def CycleDeletion : Prop := ∀ (n g : ℕ) (G : SimpleGraph (Fin n)),
  ∃ S : Finset (Fin n), n - S.card ≤ shortCycleCount g G ∧
    NoShortCycles g (G.induce (S : Set (Fin n)))

/-- The quantitative deterministic alteration stage of W24. -/
def Alteration : Prop := ∀ (g k n : ℕ) (G : SimpleGraph (Fin n)),
  3 ≤ g → 1 ≤ k → 1 ≤ n →
  (shortCycleCount g G : ℝ) < (n : ℝ) / 2 → G.indepNum < threshold k n →
  ∃ S : Finset (Fin n),
    n - S.card ≤ shortCycleCount g G ∧
    (n : ℝ) / 2 < (S.card : ℝ) ∧
    NoShortCycles g (G.induce (S : Set (Fin n))) ∧
    ((threshold k n - 1 : ℕ) : ℝ) < (n : ℝ) / (4 * (k : ℝ)) ∧
    (∀ T : Finset (S : Set (Fin n)),
      (G.induce (S : Set (Fin n))).IsIndepSet (T : Set (S : Set (Fin n))) →
      T.card ≤ threshold k n - 1 ∧ (T.card : ℝ) < (n : ℝ) / (4 * (k : ℝ))) ∧
    ¬ (G.induce (S : Set (Fin n))).Colorable k

/-- W24: a graph on an explicitly finite vertex type, with the full conclusion. -/
def Existence : Prop := ∀ (g k : ℕ), 3 ≤ g → 1 ≤ k →
  ∃ (n : ℕ) (S : Finset (Fin n)) (G : SimpleGraph (S : Set (Fin n))),
    NoShortCycles g G ∧ (k : ℕ∞) < G.chromaticNumber

end Specs.P205.Probability.HighGirthHighChromatic
