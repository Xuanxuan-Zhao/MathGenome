import MathGenome.Internal.ExtremalOptimization.Specs.P205.Ramsey.GraphNumbers
import Mathlib.Data.Fintype.Powerset

namespace P205.Ramsey

/-- The cycle with cyclic vertex order `0,1,2,3,4`. -/
def redFiveCycleEdges : Finset (Finset (Fin 5)) :=
  {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}}

/-- The complementary cycle, with cyclic vertex order `0,2,4,1,3`. -/
def blueFiveCycleEdges : Finset (Finset (Fin 5)) :=
  {{0, 2}, {2, 4}, {4, 1}, {1, 3}, {3, 0}}

namespace Specs

def FiveCycleColorType := KSubsets (Fin 5) 2 → Fin 2

/-- Color the pentagon red (zero) and all its other edges blue (one). -/
def fiveCycleColorValue : FiveCycleColorType :=
  fun s => if s.val ∈ redFiveCycleEdges then 0 else 1

/-- Both color classes are exactly the displayed five-cycles. -/
def FiveCycleColorEdges : Prop :=
  ∀ s : KSubsets (Fin 5) 2,
    (fiveCycleColorValue s = 0 ↔ s.val ∈ redFiveCycleEdges) ∧
    (fiveCycleColorValue s = 1 ↔ s.val ∈ blueFiveCycleEdges)

/-- The explicit coloring has no triangle of either color. -/
def FiveCycleNoTriangle : Prop :=
  ∀ t : Finset (Fin 5), t.card = 3 →
    ¬ ColoredClique fiveCycleColorValue 0 t ∧
    ¬ ColoredClique fiveCycleColorValue 1 t

def RamseyThreeThreeUpper : Prop := ramseyNumberValue 3 3 ≤ 6

def RamseyThreeThreeLower : Prop := 5 < ramseyNumberValue 3 3

def RamseyThreeThree : Prop := ramseyNumberValue 3 3 = 6

end Specs
end P205.Ramsey
