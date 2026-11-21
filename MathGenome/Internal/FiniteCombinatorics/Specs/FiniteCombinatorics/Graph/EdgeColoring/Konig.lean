import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! The bipartite multigraph assertion of paper.tex, p204:W61.
Only the actual vertex and labelled-edge sets are required to be finite.
Bipartiteness is tested on the adjacency shadow; looplessness is explicit.
The palette and degree retain all edge labels, including parallel edges. -/
universe u v
namespace Specs.FiniteCombinatorics.Graph.EdgeColoring.Konig
open Specs.FiniteCombinatorics.Graph.MultigraphFoundation
open Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations

def konig_line_coloringType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Loopless]
    (h : IsFiniteValue G), (underlyingValue G).IsBipartite →
      chromaticIndexValue G = maximumDegreeValue G h

end Specs.FiniteCombinatorics.Graph.EdgeColoring.Konig
