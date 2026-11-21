import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations

/-! The simple-graph assertion of paper.tex, Theorem W61 (lines 2284–2287).
No positivity or nonemptiness assumptions are imposed. The coloring uses the
actual edge identities in the shared edge-coloring interface. -/

universe u
namespace Specs.FiniteCombinatorics.Graph.EdgeColoring.Vizing

open Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations

def vizing_colorableType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    SimpleColorableValue G (simpleMaximumDegreeValue G + 1)

def vizingType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    simpleChromaticIndexValue G ≤ simpleMaximumDegreeValue G + 1

end Specs.FiniteCombinatorics.Graph.EdgeColoring.Vizing
