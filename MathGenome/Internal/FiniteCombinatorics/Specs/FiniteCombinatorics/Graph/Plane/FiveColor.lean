import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Foundations

/-! The full conclusion of paper.tex W63 (2454–2493), including the empty graph
and disconnected graphs. Planarity is existence of the prescribed polygonal
crossing-free drawing; no order, connectivity or degree hypothesis is added. -/
universe u
namespace Specs.FiniteCombinatorics.Graph.Plane.FiveColor
open Specs.FiniteCombinatorics.Graph.Plane.Foundations

def five_colorType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    Planar G → Nonempty (G.Coloring (Fin 5))

end Specs.FiniteCombinatorics.Graph.Plane.FiveColor
