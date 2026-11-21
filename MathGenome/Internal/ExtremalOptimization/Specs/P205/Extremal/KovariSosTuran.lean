import MathGenome.Internal.ExtremalOptimization.Specs.P205.Extremal.KSTStarCount
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Finset.Lattice.Fold

namespace P205.Extremal.KovariSosTuranSpec

open Finset Filter Asymptotics

/-- The maximum over all labelled, non-induced K_(s,t)-free graphs on n vertices. -/
noncomputable def extremalEdgeCountValue (s t n : ℕ) : ℕ := by
  classical
  exact (univ.filter fun G : SimpleGraph (Fin n) =>
    IsEmpty ((completeBipartiteGraph (Fin s) (Fin t)).Copy G)).sup
      (fun G => G.edgeFinset.card)

/-- Type of the three-parameter extremal edge count. -/
def extremalEdgeCountType : Type := ℕ → ℕ → ℕ → ℕ

universe u

/-- The quantitative general-graph bound, with real powers and all boundary cases. -/
def quantitativeBound : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V],
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (s t : ℕ),
    1 ≤ s → s ≤ t →
    IsEmpty ((completeBipartiteGraph (Fin s) (Fin t)).Copy G) →
    2 * (G.edgeFinset.card : ℝ) ≤
      ((s : ℝ) - 1) * (Fintype.card V : ℝ) +
      ((t : ℝ) - 1) ^ (1 / (s : ℝ)) *
        (Fintype.card V : ℝ) ^ (2 - 1 / (s : ℝ))

/-- The extremal edge count itself has the stated fixed-parameter asymptotic order. -/
def asymptoticBound : Prop :=
  ∀ s t : ℕ, 1 ≤ s → s ≤ t →
    (fun n : ℕ => (extremalEdgeCountValue s t n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (2 - 1 / (s : ℝ)))

end P205.Extremal.KovariSosTuranSpec
