import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Foundations
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Independent statement of paper.tex, W59. The exclusions mean a complete
simple graph and an isomorphic copy of an odd cycle of length at least three.
No connectivity, regularity or minimum-degree condition is hidden in them. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Coloring.Brooks
open Specs.FiniteCombinatorics.Graph.Foundations
open Specs.FiniteCombinatorics.Graph.Coloring.Foundations

def maximumDegreeType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ

def maximumDegreeValue : maximumDegreeType := fun {V} _ G =>
  letI := Fintype.ofFinite V
  Finset.univ.sup (degreeValue G)

def brooksType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), G.Connected → G ≠ ⊤ →
    (∀ n : ℕ, 3 ≤ n → Odd n → ¬ Nonempty (G ≃g SimpleGraph.cycleGraph n)) →
    chromaticNumberValue G ≤ maximumDegreeValue G

end Specs.FiniteCombinatorics.Graph.Coloring.Brooks
